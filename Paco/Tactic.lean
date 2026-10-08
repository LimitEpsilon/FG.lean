import Paco.PacoDefs
import Lean.Elab.Tactic.ElabTerm
import Lean.Meta.Closure
import Lean.Meta.Tactic.Replace

/-!
# Paco tactics

* `pcofix cih [with r]`: start a parameterized coinduction proof.
* `pinit`, `pinit at h`: turn a predicate defined with `coinductive_fixpoint` into `plfp f ⊤ₚ`.
* `pfold`, `punfold at h`: unfold `plfp f r` into `f (uplfp f r)`.
* `pleft`, `pright`: prove `uplfp f r xs` from `r xs`, respectively `plfp f r xs`.
* `pcases at h`: turn `h : uplfp f r xs` into `h : r xs ∨ plfp f r xs`.
* `pclearbot at h`: turn `h : uplfp f ⊤ₚ xs` into `h : plfp f ⊤ₚ xs`.
* `pmon`: change the parameter of a `plfp` goal (leaves `r ⊑ ?r'` and `plfp f ?r' xs`).
* `ptop`: close a goal `x ⊑ ⊤ₚ`.

## Design

The tactics work directly on goals with the `MVarId` API: they recognize `plfp`/`uplfp`
applications, instantiate the lemmas of `Paco.PacoDefs` and replace the goal or hypothesis. They do
not run tactic scripts internally, introduce no auxiliary hypotheses and only touch the
hypothesis they are given, so they are hygienic and their behaviour does not depend on the
surrounding context.

On predicates, `x ⊑ y`, `⊤ₚ` and `uplfp` unfold pointwise to reverse implication, `False` and
`∨` by unfolding definitions of this library only (see `Paco.Lattice`). Goals produced by the
tactics never contain the lattice instances of Lean core, so they are type-correct at
`.implicit` transparency.

The only dependency on how Lean implements `coinductive_fixpoint` is in the section
"Predicates defined by `coinductive_fixpoint`" below.
-/

namespace Paco.Tactic

open Lean Meta Elab Tactic

/-! ## Recognizing `plfp` and `uplfp` -/

/-- An application `@plfp α inst f hm r x₁ ⋯ xₙ` or `@uplfp α inst f hm r x₁ ⋯ xₙ`. -/
structure PacoApp where
  /-- Universe levels of the head constant. -/
  us : List Level
  α : Expr
  inst : Expr
  f : Expr
  hm : Expr
  r : Expr
  args : Array Expr

namespace PacoApp

private def ofApp? (declName : Name) (e : Expr) : Option PacoApp :=
  if e.isAppOf declName && e.getAppNumArgs ≥ 5 then
    let xs := e.getAppArgs
    some { us := e.getAppFn.constLevels!, α := xs[0]!, inst := xs[1]!, f := xs[2]!, hm := xs[3]!,
           r := xs[4]!, args := xs.extract 5 }
  else
    none

/-- Recognize an application of `declName` (`plfp` or `uplfp`), unfolding the head of `e` if
necessary, e.g. when the functional is a definition as in `f (uplfp f r) x` with
`f X x = X (x + 1)`. `plfp` and `uplfp` themselves are never unfolded. -/
partial def match? (declName : Name) (e : Expr) (fuel : Nat := 16) : MetaM (Option PacoApp) := do
  let e := (← instantiateMVars e).cleanupAnnotations
  if let some p := ofApp? declName e then return p
  if fuel = 0 || e.isAppOf ``plfp || e.isAppOf ``uplfp then return none
  let e' ← whnfCore e
  if e' != e then return ← match? declName e' (fuel - 1)
  let some e' ← unfoldDefinition? e | return none
  match? declName e' (fuel - 1)

/-- `@plfp α inst f hm r` -/
def plfpWith (p : PacoApp) (r : Expr) : Expr :=
  mkAppN (.const ``plfp p.us) #[p.α, p.inst, p.f, p.hm, r]

/-- `@uplfp α inst f hm r` -/
def uplfpWith (p : PacoApp) (r : Expr) : Expr :=
  mkAppN (.const ``uplfp p.us) #[p.α, p.inst, p.f, p.hm, r]

/-- `@CompleteLattice.le α inst x y` -/
def le (p : PacoApp) (x y : Expr) : Expr :=
  mkAppN (.const ``CompleteLattice.le p.us) #[p.α, p.inst, x, y]

/-- `@CompleteLattice.top α inst` -/
def top (p : PacoApp) : Expr :=
  mkAppN (.const ``CompleteLattice.top p.us) #[p.α, p.inst]

/-- Apply a lemma `@c α inst f hm` of `Paco.PacoDefs` to further arguments. -/
def lemma (p : PacoApp) (c : Name) (args : Array Expr := #[]) : Expr :=
  mkAppN (.const c p.us) (#[p.α, p.inst, p.f, p.hm] ++ args)

/-- `r x₁ ⋯ xₙ ∨ plfp f r x₁ ⋯ xₙ`, which `uplfp f r x₁ ⋯ xₙ` unfolds to. -/
def uplfpDisj (p : PacoApp) : Expr :=
  mkOr (mkAppN p.r p.args) (mkAppN (p.plfpWith p.r) p.args)

end PacoApp

/-- From `h : a = b`, build `h' : a x₁ ⋯ xₙ = b x₁ ⋯ xₙ`. -/
def mkCongrFunN (h : Expr) (xs : Array Expr) : MetaM Expr :=
  xs.foldlM mkCongrFun h

/-- Replace hypothesis `fvarId` by a new hypothesis of type `typeNew` with the same name, given
`proof : typeNew` (which may refer to `fvarId`). -/
def replaceHyp (goal : MVarId) (fvarId : FVarId) (typeNew proof : Expr) : MetaM MVarId :=
  goal.withContext do
    let userName ← fvarId.getUserName
    let result ← goal.assertAfter fvarId userName typeNew proof
    try result.mvarId.clear fvarId catch _ => pure result.mvarId

/-- Close `goal` with `proof`, whose type is definitionally equal to the target. -/
def closeWith (goal : MVarId) (proof : Expr) : MetaM Unit := do
  goal.assign (← mkExpectedTypeHint proof (← goal.getType))

/-! ## Predicates defined by `coinductive_fixpoint`

`coinductive_fixpoint` defines a predicate `C` as `fun ps => Lean.Order.lfp_monotone F hm`, possibly
through an auxiliary `C.mutual`, where `F` is the functional and `hm` its monotonicity proof with
respect to the lattice `ReverseImplicationOrder` of Lean core. We transfer `hm` to our order via an
auxiliary theorem (the two orders are definitionally equal) and identify the least fixed point
with `plfp F ⊤ₚ` using `Paco.eq_plfp_top`. Everything that depends on this encoding is in this
section.
-/

/-- An application `C a₁ ⋯ aₘ` of a predicate defined with `coinductive_fixpoint`, together with
its translation to `plfp`. -/
structure FixpointApp where
  /-- The translation `plfp F ⊤ₚ x₁ ⋯ xₙ`. -/
  paco : Expr
  /-- A proof of `C a₁ ⋯ aₘ = plfp F ⊤ₚ x₁ ⋯ xₙ`. -/
  eq : Expr

/-- Unfold the head constant of `e`, even if it is irreducible. -/
private def unfoldHead? (e : Expr) : MetaM (Option Expr) := do
  let .const c us := e.getAppFn | return none
  let some (.defnInfo info) := (← getEnv).find? c | return none
  let value := info.value.instantiateLevelParams info.levelParams us
  return some (value.betaRev e.getAppRevArgs).headBeta

private def isLfpApp (e : Expr) : Bool :=
  e.isAppOf ``Lean.Order.lfp_monotone && e.getAppNumArgs ≥ 4

/-- Unfold the head of `e` until it is an application of `Lean.Order.lfp_monotone`. -/
private partial def unfoldToLfp (e : Expr) (fuel : Nat := 8) : MetaM Expr := do
  if isLfpApp e || fuel = 0 then return e
  let some e' ← unfoldHead? e | return e
  unfoldToLfp e' (fuel - 1)

/-- Recognize an application of a predicate defined with `coinductive_fixpoint` and translate it
to `plfp`. Returns `none` if `e` is not such an application. -/
def FixpointApp.match? (e : Expr) : MetaM (Option FixpointApp) := do
  let e := (← instantiateMVars e).cleanupAnnotations
  let lfpApp ← unfoldToLfp e.headBeta
  unless isLfpApp lfpApp do
    if let .proj _ _ s := lfpApp.getAppFn then
      if isLfpApp (← unfoldToLfp s) then
        throwError "paco: predicates defined by mutual `coinductive_fixpoint` are not \
          supported:{indentExpr e}"
    return none
  let xs := lfpApp.getAppArgs
  let usL := lfpApp.getAppFn.constLevels!
  let (α, instL, F, hmL, args) := (xs[0]!, xs[1]!, xs[2]!, xs[3]!, xs.extract 4)
  let us := [← getLevel α]
  let some inst ← synthInstance? (mkApp (.const ``CompleteLattice us) α) |
    throwError "paco: cannot find a `Paco.CompleteLattice` instance for{indentExpr α}"
  -- Transfer the monotonicity proof to our order. It is stored in an auxiliary theorem so that
  -- the goals we produce do not mention the lattice instances of Lean core. The kernel checks
  -- auxiliary theorems asynchronously, so we must check the transfer here.
  let monType := mkAppN (.const ``monotone us) #[α, inst, F]
  unless ← withoutModifyingState <| withTransparency .default <|
      isDefEq (← inferType hmL) monType do
    throwError "paco: expected a predicate defined with `coinductive_fixpoint`, got{indentExpr e}\n\
      which is the least fixed point of a function satisfying{indentExpr (← inferType hmL)}\n\
      instead of{indentExpr monType}"
  let hm ← mkAuxTheorem monType hmL (kind? := `_paco_mon)
  let pred := mkAppN (.const ``Lean.Order.lfp_monotone usL) #[α, instL, F, hmL]
  let hfix := mkAppN (.const ``Lean.Order.lfp_monotone_fix usL) #[α, instL, F, hmL]
  let hleast ← withLocalDeclD `x α fun x => do
    withLocalDeclD `h (mkAppN (.const ``CompleteLattice.le us) #[α, inst, mkApp F x, x]) fun h =>
      mkLambdaFVars #[x, h] <|
        mkAppN (.const ``Lean.Order.lfp_le_of_le_monotone usL) #[α, instL, F, hmL, x, h]
  let top := mkAppN (.const ``CompleteLattice.top us) #[α, inst]
  let plfpTop := mkAppN (.const ``plfp us) #[α, inst, F, hm, top]
  let eq := mkAppN (.const ``eq_plfp_top us) #[α, inst, F, hm, pred, hfix, hleast]
  let paco := mkAppN plfpTop args
  let eq ← mkExpectedTypeHint (← mkCongrFunN eq args) (← mkEq e paco)
  return some { paco, eq }

/-! ## `pinit` -/

/-- Transform the conclusion `c` of `∀ x₁ ⋯ xₙ, c` along `k c = some (c', proof of c = c')`.
Returns `∀ x₁ ⋯ xₙ, c'` and a function mapping a proof of `∀ x₁ ⋯ xₙ, c` to a proof of
`∀ x₁ ⋯ xₙ, c'` (if `mp`) or conversely. -/
private def transformConclusion? (type : Expr) (k : Expr → MetaM (Option (Expr × Expr))) :
    MetaM (Option (Expr × (Bool → Expr → MetaM Expr))) := do
  let type ← instantiateMVars type
  let some (typeNew, eqs) ← forallTelescope type fun xs c => do
      let some (c', eq) ← k c | return none
      return some (← mkForallFVars xs c', ← mkLambdaFVars xs eq)
    | return none
  let convert (mp : Bool) (h : Expr) : MetaM Expr :=
    forallTelescope type fun xs _ => do
      let eq := eqs.beta xs
      mkLambdaFVars xs <| ← if mp then mkEqMP eq (h.beta xs) else mkEqMPR eq (h.beta xs)
  return some (typeNew, convert)

private def toPaco? (c : Expr) : MetaM (Option (Expr × Expr)) := do
  let some fp ← FixpointApp.match? c | return none
  return some (fp.paco, fp.eq)

private def pinitError (e : Expr) : MetaM α :=
  throwError "pinit: expected a predicate defined with `coinductive_fixpoint`, got{indentExpr e}"

/-- Replace the conclusion `C a₁ ⋯ aₘ` of the goal by `plfp F ⊤ₚ x₁ ⋯ xₙ`, if `C` is defined with
`coinductive_fixpoint`. -/
def pinitTarget? (goal : MVarId) : MetaM (Option MVarId) := goal.withContext do
  let some (targetNew, convert) ← transformConclusion? (← goal.getType) toPaco? | return none
  let goalNew ← mkFreshExprSyntheticOpaqueMVar targetNew (← goal.getTag)
  goal.assign (← convert false goalNew)
  return goalNew.mvarId!

/-- `pinit` -/
def pinitTarget (goal : MVarId) : MetaM MVarId := do
  let some goal' ← pinitTarget? goal | pinitError (← goal.getType)
  return goal'

/-- `pinit at h` -/
def pinitHyp (goal : MVarId) (fvarId : FVarId) : MetaM MVarId := goal.withContext do
  let type ← fvarId.getType
  let some (typeNew, convert) ← transformConclusion? type toPaco? | pinitError type
  replaceHyp goal fvarId typeNew (← convert true (.fvar fvarId))

/-! ## `pfold`, `punfold`, `pclearbot`, `pcases` -/

private def expectPlfp (tac : MessageData) (e : Expr) : MetaM PacoApp := do
  let some p ← PacoApp.match? ``plfp e |
    throwError "{tac}: expected `plfp f r x₁ ⋯ xₙ`, got{indentExpr e}"
  return p

private def expectUplfp (tac : MessageData) (e : Expr) : MetaM PacoApp := do
  let some p ← PacoApp.match? ``uplfp e |
    throwError "{tac}: expected `uplfp f r x₁ ⋯ xₙ`, got{indentExpr e}"
  return p

/-- `plfp f r xs = f (uplfp f r) xs` -/
private def unfoldEq (p : PacoApp) : MetaM (Expr × Expr) := do
  let rhs := (mkAppN (mkApp p.f (p.uplfpWith p.r)) p.args).headBeta
  return (rhs, ← mkCongrFunN (p.lemma ``plfp_unfold #[p.r]) p.args)

/-- `pfold`: replace the goal `plfp f r xs` by `f (uplfp f r) xs`. -/
def pfold (goal : MVarId) : MetaM MVarId := goal.withContext do
  let p ← expectPlfp "pfold" (← goal.getType)
  let (targetNew, eq) ← unfoldEq p
  goal.replaceTargetEq targetNew eq

/-- `punfold at h`: replace `h : plfp f r xs` by `h : f (uplfp f r) xs`. -/
def punfold (goal : MVarId) (fvarId : FVarId) : MetaM MVarId := goal.withContext do
  let p ← expectPlfp "punfold" (← fvarId.getType)
  let (typeNew, eq) ← unfoldEq p
  return (← goal.replaceLocalDecl fvarId typeNew eq).mvarId

/-- `pclearbot at h`: replace `h : uplfp f ⊤ₚ xs` by `h : plfp f ⊤ₚ xs`. -/
def pclearbot (goal : MVarId) (fvarId : FVarId) : MetaM MVarId := goal.withContext do
  let p ← expectUplfp "pclearbot" (← fvarId.getType)
  unless ← isDefEq p.r p.top do
    throwError "pclearbot: the parameter{indentExpr p.r}\nis not `⊤ₚ`"
  let typeNew := mkAppN (p.plfpWith p.top) p.args
  let eq ← mkCongrFunN (p.lemma ``uplfp_top) p.args
  return (← goal.replaceLocalDecl fvarId typeNew eq).mvarId

/-- Check that `e`, which is `uplfp f r xs` up to unfolding, unfolds to the disjunction
`r xs ∨ plfp f r xs`. -/
private def uplfpDisj (tac : MessageData) (p : PacoApp) (e : Expr) : MetaM Expr := do
  let disj := p.uplfpDisj
  unless ← isDefEq e disj do
    throwError "{tac}: failed to unfold{indentExpr e}\nto{indentExpr disj}"
  return disj

/-- `pcases at h`: replace `h : uplfp f r xs` by `h : r xs ∨ plfp f r xs`. -/
def pcases (goal : MVarId) (fvarId : FVarId) : MetaM MVarId := goal.withContext do
  let type ← fvarId.getType
  let p ← expectUplfp "pcases" type
  goal.replaceLocalDeclDefEq fvarId (← uplfpDisj "pcases" p type)

/-! ## `pleft`, `pright`, `pmon`, `ptop` -/

/-- `pleft` (`left := true`): replace the goal `uplfp f r xs` by `r xs`.
`pright` (`left := false`): replace the goal `uplfp f r xs` by `plfp f r xs`. -/
def psplit (goal : MVarId) (left : Bool) : MetaM MVarId := goal.withContext do
  let tac := if left then "pleft" else "pright"
  let target ← goal.getType
  let p ← expectUplfp tac target
  let disj ← uplfpDisj tac p target
  let some (a, b) := disj.app2? ``Or | unreachable!
  let goalNew ← mkFreshExprSyntheticOpaqueMVar (if left then a else b) (← goal.getTag)
  closeWith goal (mkApp3 (.const (if left then ``Or.inl else ``Or.inr) []) a b goalNew)
  return goalNew.mvarId!

/-- `pmon`: for a goal `plfp f r xs`, create the goals `plfp f ?r' xs`, `r ⊑ ?r'` and `?r'`.
The `plfp` goal comes first (as in Coq's `paco_mon`), so that in `pmon <;> try assumption` the
parameter `?r'` is determined by a `plfp` hypothesis rather than by an arbitrary hypothesis that
happens to unify with `r ⊑ ?r'`. -/
def pmon (goal : MVarId) : MetaM (List MVarId) := goal.withContext do
  let p ← expectPlfp "pmon" (← goal.getType)
  let r' ← mkFreshExprMVar p.α (userName := `r')
  let hle ← mkFreshExprSyntheticOpaqueMVar (p.le p.r r') (← goal.getTag)
  let hpaco ← mkFreshExprSyntheticOpaqueMVar (mkAppN (p.plfpWith r') p.args) (← goal.getTag)
  -- `plfp_mon hm r r' hle : plfp f r ⊑ plfp f r'`, which unfolds to
  -- `∀ xs, plfp f r' xs → plfp f r xs`
  closeWith goal <| mkApp (mkAppN (p.lemma ``plfp_mon #[p.r, r', hle]) p.args) hpaco
  return [hpaco.mvarId!, hle.mvarId!, r'.mvarId!]

/-- `ptop`: close a goal `x ⊑ ⊤ₚ`. -/
def ptop (goal : MVarId) : MetaM Unit := goal.withContext do
  let target ← whnfR (← instantiateMVars (← goal.getType))
  let some (α, inst, x, t) := target.app4? ``CompleteLattice.le |
    throwError "ptop: expected a goal of the form `x ⊑ ⊤ₚ`, got{indentExpr target}"
  let us := target.getAppFn.constLevels!
  unless ← isDefEq t (mkAppN (.const ``CompleteLattice.top us) #[α, inst]) do
    throwError "ptop: expected a goal of the form `x ⊑ ⊤ₚ`, got{indentExpr target}"
  closeWith goal (mkAppN (.const ``CompleteLattice.top_spec us) #[α, inst, x])

/-! ## `pcofix` -/

/-- `pcofix cih with φ` on a goal `∀ ys, c`, where `c` is `C es` (for a predicate `C` defined with
`coinductive_fixpoint`) or `plfp f r es`. Produces a goal `∀ ys, plfp f φ es` with hypotheses
`φ` and `cih : ∀ ys, φ es` (and `φ ⊑ r` unless `r` is `⊤ₚ`).

Writing `Q := fun p => ∀ ys, p es`, this applies `plfp_cofix` with `l := fun xs => ∀ q, Q q → q xs`,
the least predicate satisfying `Q`. -/
def pcofix (goal : MVarId) (cihName φName : Name) : MetaM MVarId := do
  let goal ← goal.withContext do
    let isPaco ← forallTelescope (← instantiateMVars (← goal.getType)) fun _ c =>
      return (← PacoApp.match? ``plfp c).isSome
    if isPaco then pure goal else
    let some goal' ← pinitTarget? goal |
      throwError "pcofix: expected a goal of the form `∀ x₁ ⋯ xₘ, C e₁ ⋯ eₙ`, where `C` is \
        defined with `coinductive_fixpoint`, or `∀ x₁ ⋯ xₘ, plfp f r e₁ ⋯ eₙ`, got{indentExpr
        (← goal.getType)}"
    pure goal'
  goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let (p, Q, l, hQ) ← forallTelescope target fun ys c => do
    let p ← expectPlfp "pcofix" c
    for e in [p.α, p.inst, p.f, p.hm, p.r] do
      if e.hasAnyFVar (ys.contains <| .fvar ·) then
        throwError "pcofix: the coinductive predicate{indentExpr (p.plfpWith p.r)}\n\
          depends on variables quantified in the goal; introduce them first"
    let es := p.args
    let n := es.size
    -- Q := fun p => ∀ ys, p es
    let Q ← withLocalDeclD `p p.α fun q => do mkLambdaFVars #[q] (← mkForallFVars ys (mkAppN q es))
    -- l := fun xs => ∀ q, Q q → q xs
    let l ← forallBoundedTelescope p.α n fun xs _ => withLocalDeclD `q p.α fun q => do
      mkLambdaFVars xs (← mkForallFVars #[q] (← mkArrow (Q.beta #[q]) (mkAppN q xs)))
    -- hQ : ∀ p, Q p ↔ p ⊑ l, where `p ⊑ l` unfolds to `∀ xs, l xs → p xs`
    let hQ ← withLocalDeclD `p p.α fun q => do
      let lhs := Q.beta #[q]
      let rhs := p.le q l
      let mp ← withLocalDeclD `hq lhs fun hq => do
        let body ← forallBoundedTelescope p.α n fun xs _ =>
          withLocalDeclD `hl (l.beta xs) fun hl => mkLambdaFVars (xs.push hl) (mkApp2 hl q hq)
        mkLambdaFVars #[hq] body
      let mpr ← withLocalDeclD `h rhs fun h => do
        let hl ← withLocalDeclD `q p.α fun q' => withLocalDeclD `hq (Q.beta #[q']) fun hq =>
          mkLambdaFVars #[q', hq] (mkAppN hq ys)
        mkLambdaFVars #[h] (← mkLambdaFVars ys (mkApp (mkAppN h es) hl))
      mkLambdaFVars #[q] (mkApp4 (.const ``Iff.intro []) lhs rhs mp mpr)
    return (p, Q, l, hQ)
  -- obg : ∀ φ, φ ⊑ r → Q φ → Q (plfp f φ)
  let incName ← mkFreshUserName `inc
  let obgType ← withLocalDeclD φName p.α fun φ => withLocalDeclD incName (p.le φ p.r) fun inc =>
    withLocalDeclD cihName (Q.beta #[φ]) fun cih => do
      mkForallFVars #[φ, inc, cih] (Q.beta #[p.plfpWith φ])
  let obg ← mkFreshExprSyntheticOpaqueMVar obgType (← goal.getTag)
  closeWith goal (p.lemma ``plfp_cofix #[p.r, Q, l, hQ, obg])
  let (fvars, goal) ← obg.mvarId!.introNP 3
  if p.r.isAppOfArity ``CompleteLattice.top 2 then goal.clear fvars[1]! else pure goal

/-! ## Syntax -/

/--
`pcofix cih` starts a proof by parameterized coinduction. The goal must have the form
`∀ x₁ ⋯ xₘ, C e₁ ⋯ eₙ`, where `C` is defined with `coinductive_fixpoint`, or
`∀ x₁ ⋯ xₘ, plfp f r e₁ ⋯ eₙ`. It introduces a predicate `φ` and the coinductive hypothesis
`cih : ∀ x₁ ⋯ xₘ, φ e₁ ⋯ eₙ`, and leaves the goal `∀ x₁ ⋯ xₘ, plfp f φ e₁ ⋯ eₙ`.
If the parameter `r` of the original goal is not `⊤ₚ`, an (inaccessible) hypothesis `φ ⊑ r` is
added as well.

`pcofix cih with r` names the predicate `r` instead of `φ`.
-/
syntax (name := pcofixStx) "pcofix " ident (" with " ident)? : tactic

/-- `pinit` replaces the conclusion `C a₁ ⋯ aₘ` of the goal, where `C` is defined with
`coinductive_fixpoint` with functional `F`, by `plfp F ⊤ₚ x₁ ⋯ xₙ`.
`pinit at h` does the same for the hypothesis `h`. -/
syntax (name := pinitStx) "pinit" (" at " ident)? : tactic

/-- `pfold` replaces the goal `plfp f r xs` by `f (uplfp f r) xs`. -/
syntax (name := pfoldStx) "pfold" : tactic

/-- `punfold at h` replaces `h : plfp f r xs` by `h : f (uplfp f r) xs`. -/
syntax (name := punfoldStx) "punfold" " at " ident : tactic

/-- `pclearbot at h` replaces `h : uplfp f ⊤ₚ xs` by `h : plfp f ⊤ₚ xs`. -/
syntax (name := pclearbotStx) "pclearbot" " at " ident : tactic

/-- `pcases at h` replaces `h : uplfp f r xs` by `h : r xs ∨ plfp f r xs`. -/
syntax (name := pcasesStx) "pcases" " at " ident : tactic

/-- `pleft` replaces the goal `uplfp f r xs` by `r xs`. -/
syntax (name := pleftStx) "pleft" : tactic

/-- `pright` replaces the goal `uplfp f r xs` by `plfp f r xs`. -/
syntax (name := prightStx) "pright" : tactic

/-- `pmon` replaces the goal `plfp f r xs` by the goals `plfp f ?r' xs` and `r ⊑ ?r'`, where `?r'`
is a new metavariable (also returned as a goal if it remains unassigned). Typically used as
`pmon <;> try assumption` followed by `ptop`. -/
syntax (name := pmonStx) "pmon" : tactic

/-- `ptop` closes a goal `x ⊑ ⊤ₚ`. -/
syntax (name := ptopStx) "ptop" : tactic

/-- Run a tactic on the main goal that produces exactly one new goal. -/
private def run1 (tac : MVarId → MetaM MVarId) : TacticM Unit :=
  liftMetaTactic fun g => return [← tac g]

/-- Run a tactic on the main goal and the hypothesis `h`. -/
private def runAt (h : Syntax) (tac : MVarId → FVarId → MetaM MVarId) : TacticM Unit := do
  let fvarId ← getFVarId h
  run1 (tac · fvarId)

elab_rules : tactic
  | `(tactic| pcofix $cih:ident $[with $φ:ident]?) =>
    run1 (pcofix · cih.getId (φ.map (·.getId) |>.getD `φ))
  | `(tactic| pinit) => run1 pinitTarget
  | `(tactic| pinit at $h:ident) => runAt h pinitHyp
  | `(tactic| pfold) => run1 pfold
  | `(tactic| punfold at $h:ident) => runAt h punfold
  | `(tactic| pclearbot at $h:ident) => runAt h pclearbot
  | `(tactic| pcases at $h:ident) => runAt h pcases
  | `(tactic| pleft) => run1 (psplit · true)
  | `(tactic| pright) => run1 (psplit · false)
  | `(tactic| pmon) => liftMetaTactic pmon
  | `(tactic| ptop) => liftMetaTactic fun g => do ptop g; return []

end Paco.Tactic
