import Paco.Tower
import Paco.Tactic
import Lean.Meta.Transform

/-!
# Tower induction tactics

* `tcofix cih [with x [hx]]`: start a proof by tower induction.
* `tstep`: on a goal `x xs` for a tower element `x`, unfold once more (`f x xs`).
* `tbase h`: close `x xs` or `f x xs` with `h : C xs`, where `C` is the coinductive predicate.

On a goal `∀ ys, C es`, where `C` is any predicate defined with `coinductive_fixpoint` (or with the
`coinductive` command) with functional `f`, `tcofix cih` introduces a tower element `x` of `f` with
`hx : Tower f x` and `cih : ∀ ys, x es`, and leaves the goal `∀ ys, f x es`. Inside `f x es`, the
recursive occurrences are `x` itself, which can be proven by `cih`, by `tstep` (`x` is closed under
`f`), by `tbase` (`x` contains `C`), or by any lemma about tower elements (up-to techniques, see
`Paco.Tower.closed`).

Compared to `pcofix`, there is no `uplfp` layer: `pfold` is part of `tcofix`, `pleft; exact cih …`
becomes `exact cih …`, `pright; pfold` becomes `tstep`, and `pinit at h; pmon …; ptop` becomes
`tbase h`.

`tcofix` can be nested: on a goal `∀ ys, x es` for a tower element `x` (for instance after
generalizing a recursive occurrence), `tcofix cih'` uses parameterized tower induction
(`Paco.Tower.cofix`). It introduces a new tower element `z` containing `x`, and transports every
hypothesis `∀ ws, x es'` (such as the outer coinductive hypothesis) to `z`. Since this also works
on a tower element given as a hypothesis, lemmas about tower elements can be proven by coinduction
and used modularly.
-/

namespace Paco.Tactic

open Lean Meta Elab Tactic

/-- A hypothesis `hx : Tower f x`. -/
structure TowerHyp extends Functional where
  x : Expr
  hx : Expr

/-- The hypotheses `hx : Tower f x` in the local context, most recent first. -/
def towerHyps : MetaM (Array TowerHyp) := do
  let mut hyps := #[]
  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    let type ← instantiateMVars decl.type
    if type.isAppOfArity ``Tower 5 then
      let xs := type.getAppArgs
      hyps := hyps.push { us := type.getAppFn.constLevels!, α := xs[0]!, inst := xs[1]!,
                          f := xs[2]!, hm := xs[3]!, x := xs[4]!, hx := decl.toExpr }
  return hyps.reverse

namespace TowerHyp

/-- Apply a lemma `@c α inst f hm x hx` of `Paco.Tower`. -/
def lemma (t : TowerHyp) (c : Name) : Expr :=
  mkAppN (.const c t.us) #[t.α, t.inst, t.f, t.hm, t.x, t.hx]

/-- `f x` as a tower element: `Tower.step hx : Tower f (f x)`. -/
def stepHyp (t : TowerHyp) : TowerHyp :=
  { t with x := mkApp t.f t.x, hx := mkAppN (.const ``Tower.step t.us) #[t.α, t.inst, t.f, t.hm, t.x, t.hx] }

end TowerHyp

/-- `f x es`, beta-reduced. -/
private def mkStep (f x : Expr) (es : Array Expr) : MetaM Expr :=
  Core.betaReduce (mkAppN (mkApp f x) es)

/-! ## `tcofix` -/

private def toLfp? (c : Expr) : MetaM (Option (Expr × Expr)) := do
  let some fp ← FixpointApp.match? c | return none
  return some (fp.lfp, fp.eqLfp)

/-- `tcofix cih with x hx` on a goal `∀ ys, C es`. Produces the goal `∀ ys, f x es` with hypotheses
`x`, `hx : Tower f x` and `cih : ∀ ys, x es`, by applying `tower_cofix` with
`Q := fun p => ∀ ys, p es`. -/
private def tcofixTop (goal : MVarId) (cihName xName hxName : Name) : MetaM MVarId :=
  goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let some (_, convert) ← transformConclusion? target toLfp? |
    throwError "tcofix: expected a goal of the form `∀ x₁ ⋯ xₘ, C e₁ ⋯ eₙ`, where `C` is defined \
      with `coinductive_fixpoint` or `coinductive`, or `∀ x₁ ⋯ xₘ, x e₁ ⋯ eₙ` for a tower element \
      `x`, got{indentExpr target}"
  let (F, Q, l, hQ) ← forallTelescope target fun ys c => do
    let some fp ← FixpointApp.match? c | unreachable!
    let F := fp.toFunctional
    for e in [F.α, F.inst, F.f, F.hm] do
      if e.hasAnyFVar (ys.contains <| .fvar ·) then
        throwError "tcofix: the functional{indentExpr F.f}\ndepends on variables quantified in \
          the goal; introduce them first"
    let (Q, l, hQ) ← mkDownSet F.us F.α F.inst ys fp.args
    return (F, Q, l, hQ)
  -- step : ∀ x, Tower f x → Q x → Q (f x)
  let stepType ← withLocalDeclD xName F.α fun x => do
    let tower := mkAppN (.const ``Tower F.us) #[F.α, F.inst, F.f, F.hm, x]
    withLocalDeclD hxName tower fun hx => withLocalDeclD cihName (Q.beta #[x]) fun cih => do
      mkForallFVars #[x, hx, cih] (← Core.betaReduce (Q.beta #[mkApp F.f x]))
  let step ← mkFreshExprSyntheticOpaqueMVar stepType (← goal.getTag)
  let proof := mkAppN (.const ``tower_cofix F.us) #[F.α, F.inst, F.f, F.hm, Q, l, hQ, step]
  goal.assign (← convert false proof)
  let (_, goal) ← step.mvarId!.introNP 3
  return goal

/-- Replace each hypothesis `h : ∀ ws, x es`, in which `x` occurs only as the head of the
conclusion, by `h : ∀ ws, z es`, using `hle : ∀ as, x as → z as`. The new hypotheses are added at
the end of the context. -/
private def transportHyps (goal : MVarId) (x z hle : Expr) : MetaM MVarId := goal.withContext do
  let some xId := x.fvarId? | return goal
  let mut hyps := #[]
  let mut olds := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let type ← instantiateMVars decl.type
    let some (type, value) ← forallTelescope type fun ws c => do
        let c := c.cleanupAnnotations
        let es := c.getAppArgs
        unless c.getAppFn == x do return none
        for e in es ++ (← ws.mapM inferType) do
          if e.containsFVar xId then return none
        return some (← mkForallFVars ws (mkAppN z es),
          ← mkLambdaFVars ws (mkApp (mkAppN hle es) (mkAppN decl.toExpr ws)))
      | continue
    hyps := hyps.push { userName := decl.userName, type, value }
    olds := olds.push decl.fvarId
  let (_, goal) ← goal.assertHypotheses hyps
  goal.tryClearMany olds

/-- Nested `tcofix cih with z hz` on a goal `∀ ys, x es`, where `hx : Tower f x`. Produces the goal
`∀ ys, f z es` with hypotheses `z`, `hz : Tower f z`, `hle : ∀ as, x as → z as` and
`cih : ∀ ys, z es`, by applying `Tower.cofix`. Hypotheses `∀ ws, x es'` (such as the coinductive
hypothesis of the enclosing `tcofix`) are transported to `z`. -/
private def tcofixNested (goal : MVarId) (t : TowerHyp) (cihName zName hzName : Name) :
    MetaM MVarId := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let (Q, l, hQ, n) ← forallTelescope target fun ys c => do
    let es := c.cleanupAnnotations.getAppArgs
    let (Q, l, hQ) ← mkDownSet t.us t.α t.inst ys es
    return (Q, l, hQ, es.size)
  let hleName ← mkFreshUserName `hle
  -- step : ∀ z, Tower f z → (∀ as, x as → z as) → Q z → Q (f z)
  let stepType ← withLocalDeclD zName t.α fun z => do
    let tower := mkAppN (.const ``Tower t.us) #[t.α, t.inst, t.f, t.hm, z]
    let incl ← forallBoundedTelescope t.α n fun as _ => do
      mkForallFVars as (← mkArrow (mkAppN t.x as) (mkAppN z as))
    withLocalDeclD hzName tower fun hz => withLocalDeclD hleName incl fun hle =>
      withLocalDeclD cihName (Q.beta #[z]) fun cih => do
        mkForallFVars #[z, hz, hle, cih] (← Core.betaReduce (Q.beta #[mkApp t.f z]))
  let step ← mkFreshExprSyntheticOpaqueMVar stepType (← goal.getTag)
  closeWith goal <|
    mkAppN (.const ``Tower.cofix t.us) #[t.α, t.inst, t.f, t.hm, t.x, t.hx, Q, l, hQ, step]
  let (fvars, goal) ← step.mvarId!.introNP 3
  let goal ← transportHyps goal t.x (.fvar fvars[0]!) (.fvar fvars[2]!)
  let (_, goal) ← goal.introNP 1
  return goal

/-- `tcofix cih with x hx`: tower induction on a goal `∀ ys, C es`, or nested tower induction on a
goal `∀ ys, x es` for a tower element `x`. -/
def tcofix (goal : MVarId) (cihName : Name) (xName? hxName? : Option Name) : MetaM MVarId :=
  goal.withContext do
  let xName := xName?.getD ((← getLCtx).getUnusedName `φ)
  let hxName ← match hxName? with
    | some n => pure n
    | none => mkFreshUserName `hx
  let nested? ← forallTelescope (← instantiateMVars (← goal.getType)) fun _ c => do
    let x := c.cleanupAnnotations.getAppFn
    return (← towerHyps).find? (·.x == x)
  match nested? with
  | some t => tcofixNested goal t cihName xName hxName
  | none => tcofixTop goal cihName xName hxName

/-! ## `tstep` and `tbase` -/

/-- `tstep`: replace the goal `x es`, where `hx : Tower f x`, by `f x es`. -/
def tstep (goal : MVarId) : MetaM MVarId := goal.withContext do
  let target := (← instantiateMVars (← goal.getType)).cleanupAnnotations
  let x := target.getAppFn
  let some t := (← towerHyps).find? (·.x == x) |
    throwError "tstep: expected a goal `x x₁ ⋯ xₙ`, where `x` is a tower element (see `tcofix`), \
      got{indentExpr target}"
  let es := target.getAppArgs
  let goalNew ← mkFreshExprSyntheticOpaqueMVar (← mkStep t.f x es) (← goal.getTag)
  -- `Tower.le_step hx : x ⊑ f x` unfolds to `∀ es, f x es → x es`
  closeWith goal (mkApp (mkAppN (t.lemma ``Tower.le_step) es) goalNew)
  return goalNew.mvarId!

/-- `tbase h`: close the goal `x es` or `f x es`, where `hx : Tower f x`, with `h : C es`, where `C`
is the coinductive predicate with functional `f`. -/
def tbase (goal : MVarId) (h : Expr) : MetaM Unit := goal.withContext do
  let hType ← instantiateMVars (← inferType h)
  let some fp ← FixpointApp.match? hType |
    throwError "tbase: expected a proof of `C x₁ ⋯ xₙ`, where `C` is defined with \
      `coinductive_fixpoint` or `coinductive`, got{indentExpr hType}"
  -- `hlfp : lfp f es`
  let hlfp ← mkEqMP fp.eqLfp h
  let target ← instantiateMVars (← goal.getType)
  for t in ← towerHyps do
    unless ← withoutModifyingState (isDefEq t.f fp.f) do continue
    -- `Tower.le_lfp hx : x ⊑ lfp f` unfolds to `∀ es, lfp f es → x es`, and similarly for the
    -- tower element `f x`
    for (t, expected) in [(t, mkAppN t.x fp.args), (t.stepHyp, ← mkStep t.f t.x fp.args)] do
      if ← isDefEq target expected then
        return ← closeWith goal (mkApp (mkAppN (t.lemma ``Tower.le_lfp) fp.args) hlfp)
  throwError "tbase: expected a goal `x x₁ ⋯ xₙ` or `f x x₁ ⋯ xₙ` for a tower element `x` of the \
    functional of{indentExpr hType}\ngot{indentExpr target}"

/-! ## Syntax -/

/--
`tcofix cih` starts a proof by tower induction (Schäfer and Smolka). The goal must have the form
`∀ x₁ ⋯ xₘ, C e₁ ⋯ eₙ`, where `C` is defined with `coinductive_fixpoint` or `coinductive`, with
functional `f`. It introduces a tower element `φ`, an (inaccessible) hypothesis `Tower f φ` and the
coinductive hypothesis `cih : ∀ x₁ ⋯ xₘ, φ e₁ ⋯ eₙ`, and leaves the goal
`∀ x₁ ⋯ xₘ, f φ e₁ ⋯ eₙ`.

On a goal `∀ x₁ ⋯ xₘ, x e₁ ⋯ eₙ`, where `x` is a tower element, `tcofix cih` performs nested
coinduction: it introduces a new tower element `φ` with `Tower f φ`, an (inaccessible) inclusion
`∀ as, x as → φ as` and `cih : ∀ x₁ ⋯ xₘ, φ e₁ ⋯ eₙ`, replaces each hypothesis `∀ ws, x es'` by
`∀ ws, φ es'`, and leaves the goal `∀ x₁ ⋯ xₘ, f φ e₁ ⋯ eₙ`.

`tcofix cih with x hx` names the tower element `x` and the tower hypothesis `hx`. Without a name,
the tower element is called `φ`, or a variant of it if `φ` is already in use.
-/
syntax (name := tcofixStx) "tcofix " ident (" with " ident (ppSpace ident)?)? : tactic

/-- `tstep` replaces the goal `x xs`, for a tower element `x` of `f`, by `f x xs`. -/
syntax (name := tstepStx) "tstep" : tactic

/-- `tbase h` closes the goal `x xs` or `f x xs`, for a tower element `x` of the functional `f` of
a coinductive predicate `C`, using `h : C xs`. -/
syntax (name := tbaseStx) "tbase " term : tactic

elab_rules : tactic
  | `(tactic| tcofix $cih:ident $[with $x:ident $[$hx:ident]?]?) =>
    liftMetaTactic fun g => do
      return [← tcofix g cih.getId (x.map (·.getId)) (hx.join.map (·.getId))]
  | `(tactic| tstep) => liftMetaTactic fun g => return [← tstep g]
  | `(tactic| tbase $h) => withMainContext do
    let h ← elabTerm h none
    liftMetaTactic fun g => do tbase g h; return []

end Paco.Tactic
