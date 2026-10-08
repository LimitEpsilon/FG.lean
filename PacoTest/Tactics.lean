import Paco

/-!
Tests: behaviour of the individual tactics, hygiene and error reporting.
-/

set_option warningAsError true
set_option linter.tacticCheckInstances true
set_option linter.unusedVariables false

namespace PacoTest.Tactics

def Bisim (s t : Nat → Nat) : Prop :=
  s 0 = t 0 ∧ Bisim (fun n => s (n + 1)) (fun n => t (n + 1))
  coinductive_fixpoint

/-- The lattice of binary relations on streams, for stating expected goals. -/
abbrev Rel := (Nat → Nat) → (Nat → Nat) → Prop

/-- A functional on unary predicates, together with its monotonicity proof. -/
def shift (X : Nat → Prop) (n : Nat) : Prop := X (n + 1)

theorem shift_mon : Paco.monotone shift := fun _ _ h n => h (n + 1)

/-! ## `pinit` -/

theorem bisim_refl : ∀ s, Bisim s s := by
  pcofix cih
  intro s
  pfold
  exact ⟨rfl, by pleft; exact cih _⟩

/-- `pinit` acts on the conclusion of the goal, under binders; `pcofix` accepts the result. -/
example : ∀ s, Bisim s s := by
  pinit
  guard_target =~ ∀ s, plfp (α := Rel) _ ⊤ₚ s s
  pcofix cih
  guard_hyp cih :ₛ ∀ s, φ s s
  intro s
  pfold
  exact ⟨rfl, by pleft; exact cih _⟩

/-- `pinit at h` acts on the conclusion of `h`, under binders. -/
example (h : ∀ s, Bisim s s) (s : Nat → Nat) : Bisim s s := by
  pinit at h
  guard_hyp h : ∀ s, plfp (α := Rel) _ ⊤ₚ s s
  pinit
  exact h s

/-- Only the given hypothesis is affected, also if it is shadowed. -/
example (s t : Nat → Nat) (h : Bisim s t) (h : Bisim t s) : True := by
  pinit at h
  rename_i h'
  guard_hyp h' :ₛ Bisim s t
  trivial

/-! ## `pfold`, `punfold`, `pcases`, `pclearbot` -/

example (s t : Nat → Nat) (h : Bisim s t) : Bisim (fun n => s (n + 1)) (fun n => t (n + 1)) := by
  pinit at h
  punfold at h
  guard_hyp h : s 0 = t 0 ∧ uplfp (α := Rel) _ ⊤ₚ (fun n => s (n + 1)) (fun n => t (n + 1))
  obtain ⟨_, h⟩ := h
  pcases at h
  guard_hyp h : (⊤ₚ : Rel) (fun n => s (n + 1)) (fun n => t (n + 1)) ∨
    plfp (α := Rel) _ ⊤ₚ (fun n => s (n + 1)) (fun n => t (n + 1))
  rcases h with h | h
  · -- the left disjunct `⊤ₚ xs` unfolds to `False`
    exact nomatch h
  · pinit; exact h

example (s t : Nat → Nat) (h : Bisim s t) : Bisim (fun n => s (n + 1)) (fun n => t (n + 1)) := by
  pinit at h
  punfold at h
  obtain ⟨_, h⟩ := h
  pclearbot at h
  guard_hyp h : plfp (α := Rel) _ ⊤ₚ (fun n => s (n + 1)) (fun n => t (n + 1))
  pinit
  exact h

/-! ## `pcofix`, `pleft`, `pright` -/

/-- The names introduced by `pcofix`, and its goal. -/
example : ∀ s, Bisim s s := by
  pcofix cih
  guard_hyp cih :ₛ ∀ s, φ s s
  guard_target =~ ∀ s, plfp (α := Rel) _ φ s s
  intro s
  pfold
  guard_target =~ s 0 = s 0 ∧ uplfp (α := Rel) _ φ (fun n => s (n + 1)) (fun n => s (n + 1))
  refine ⟨rfl, ?_⟩
  pleft
  guard_target =ₛ φ (fun n => s (n + 1)) (fun n => s (n + 1))
  exact cih _

/-- `pcofix cih with R` names the predicate. -/
example : ∀ s, Bisim s s := by
  pcofix ih with R
  guard_hyp ih :ₛ ∀ s, R s s
  intro s
  pfold
  exact ⟨rfl, by pleft; exact ih _⟩

/-- `pright` continues the coinduction without using the coinductive hypothesis. -/
example : ∀ s, Bisim s s := by
  pcofix cih
  intro s
  pfold
  refine ⟨rfl, ?_⟩
  pright
  guard_target =~ plfp (α := Rel) _ φ (fun n => s (n + 1)) (fun n => s (n + 1))
  pfold
  exact ⟨rfl, by pleft; exact cih _⟩

/-- The tactics leave unrelated hypotheses alone, whatever their names. -/
example (hx : (fun x : Nat => x) 1 = 1) (h x : True) (hinit hunfold unpacker converter : 1 = 1) :
    ∀ s, Bisim s s := by
  pcofix cih
  guard_hyp hx :ₛ (fun x : Nat => x) 1 = 1
  guard_hyp h :ₛ True
  guard_hyp unpacker :ₛ 1 = 1
  intro s
  pfold
  refine ⟨rfl, ?_⟩
  pleft
  guard_hyp hx :ₛ (fun x : Nat => x) 1 = 1
  exact cih _

/-- Names chosen by `pcofix` inside a macro are hygienic. -/
macro "bisim_refl_tac" : tactic =>
  `(tactic| (pcofix cih; intro s; pfold; exact ⟨rfl, by pleft; exact cih _⟩))

example (cih : False → False) : ∀ s, Bisim s s := by
  bisim_refl_tac

/-- A goal already of the form `plfp f r xs` with a parameter `r` other than `⊤ₚ`:
`pcofix` keeps the (inaccessible) hypothesis `φ ⊑ r`. -/
example (r : Nat → Prop) (hr : ∀ n, r n) : ∀ n, plfp shift (hm := shift_mon) r n := by
  pcofix cih
  rename_i inc
  guard_hyp inc : φ ⊑ r
  intro n
  pfold
  pleft
  exact inc _ (hr _)

/-! ## `pmon`, `ptop` -/

/-- `pmon` puts the `plfp` goal first, so `try assumption` does not instantiate the parameter
with `cih` (which unifies with `φ ⊑ Bisim`). -/
example : ∀ s t, Bisim s t → Bisim s t := by
  pcofix cih
  intro s t h
  pinit at h
  pmon <;> try assumption
  guard_target =~ φ ⊑ ⊤ₚ
  ptop

example (r : (Nat → Nat) → (Nat → Nat) → Prop) (s : Nat → Nat) : r ⊑ ⊤ₚ := by
  ptop

/-! ## Errors -/

example (s : Nat → Nat) : Bisim s s := by
  fail_if_success pfold
  fail_if_success pleft
  fail_if_success pright
  fail_if_success pmon
  fail_if_success ptop
  pinit
  fail_if_success pinit
  fail_if_success pleft
  pfold
  refine ⟨rfl, ?_⟩
  fail_if_success pfold
  pright
  fail_if_success pright
  have h := bisim_refl fun n => s (n + 1)
  pinit at h
  exact h

example (s : Nat → Nat) (h₁ : True) (h₂ : uplfp shift (hm := shift_mon) (fun _ => True) 0) :
    True := by
  fail_if_success punfold at h₁
  fail_if_success pcases at h₁
  fail_if_success pclearbot at h₁
  fail_if_success pinit at h₁
  -- the parameter is not `⊤ₚ`
  fail_if_success pclearbot at h₂
  trivial

/-- The predicate may not depend on variables quantified in the goal. -/
def BisimT {α : Type} (s t : Nat → α) : Prop :=
  s 0 = t 0 ∧ BisimT (fun n => s (n + 1)) (fun n => t (n + 1))
  coinductive_fixpoint

/--
error: pcofix: the coinductive predicate
  plfp (fun f s t => s 0 = t 0 ∧ f (fun n => s (n + 1)) fun n => t (n + 1)) ⊤ₚ
depends on variables quantified in the goal; introduce them first
-/
#guard_msgs in
example : ∀ (α : Type) (s : Nat → α), BisimT s s := by
  pcofix cih

def Ind (n : Nat) : Prop := n = 0 ∨ Ind (n - 1)
  inductive_fixpoint

/--
error: paco: expected a predicate defined with `coinductive_fixpoint`, got
  Ind 3
which is the least fixed point of a function satisfying
  Lean.Order.monotone fun f n => n = 0 ∨ f (n - 1)
instead of
  Paco.monotone fun f n => n = 0 ∨ f (n - 1)
-/
#guard_msgs in
example (h : Ind 3) : True := by
  pinit at h

mutual
def Ev (n : Nat) : Prop := Od (n + 1)
  coinductive_fixpoint
def Od (n : Nat) : Prop := Ev (n + 1)
  coinductive_fixpoint
end

/--
error: paco: predicates defined by mutual `coinductive_fixpoint` are not supported:
  Ev n
-/
#guard_msgs in
example : ∀ n, Ev n := by
  pcofix cih

end PacoTest.Tactics
