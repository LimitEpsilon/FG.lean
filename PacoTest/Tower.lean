import Paco

/-!
Tests: the tower induction tactics `tcofix`, `tstep` and `tbase`.
-/

set_option warningAsError true
set_option linter.tacticCheckInstances true
set_option linter.unusedVariables false

namespace PacoTest.Tower

/-! ## Shapes of coinductive predicates -/

def Always : Prop := Always ∧ True
  coinductive_fixpoint

theorem always : Always := by
  tcofix cih
  guard_target =ₛ φ ∧ True
  exact ⟨cih, trivial⟩

def Inf (n : Nat) : Prop := Inf (n + 1)
  coinductive_fixpoint

theorem inf : ∀ n, Inf n := by
  tcofix cih
  guard_hyp cih :ₛ ∀ n, φ n
  guard_target =ₛ ∀ n, φ (n + 1)
  exact fun n => cih _

def DepP (α : Type) (n : Nat) (v : Fin (n + 1)) : Prop := DepP α (n + 1) v.castSucc
  coinductive_fixpoint

theorem depP (α : Type) : ∀ n v, DepP α n v := by
  tcofix cih
  exact fun n v => cih _ _

def NP (n : Nat) (x : Bool) : Prop := NP (n + 1) x
  coinductive_fixpoint

theorem np (x : Bool) : ∀ n, NP n x := by
  tcofix cih
  exact fun n => cih _

def PM : Nat → Prop
  | 0 => PM 1
  | n + 1 => PM n ∧ True
  coinductive_fixpoint

theorem pm : ∀ n, PM n := by
  tcofix cih
  intro n
  cases n with
  | zero => exact cih 1
  | succ n => exact ⟨cih n, trivial⟩

/-- Predicates defined with the `coinductive` command: goals are in the existential form of
`infSeq.coinduct`. -/
coinductive infSeq (r : Nat → Nat → Prop) : Nat → Prop where
  | step : r a b → infSeq r b → infSeq r a

theorem infSeq_succ : ∀ n, infSeq (fun a b => b = a + 1) n := by
  tcofix cih
  intro n
  guard_target =ₛ ∃ b, b = n + 1 ∧ φ b
  exact ⟨_, rfl, cih _⟩

coinductive Stutter : Nat → Prop where
  | stay : Stutter n → Stutter n
  | next : Stutter (n + 1) → Stutter n

theorem stutter : ∀ n, Stutter n := by
  tcofix cih
  intro n
  -- unfold twice before using the coinductive hypothesis
  refine .inr ?_
  tstep
  exact .inl (cih _)

/-! ## `tstep`, `tbase`, names and hygiene -/

universe u

def Bisim {α : Type u} (s t : Nat → α) : Prop :=
  s 0 = t 0 ∧ Bisim (fun n => s (n + 1)) (fun n => t (n + 1))
  coinductive_fixpoint

theorem bisim_refl {α : Type u} : ∀ s : Nat → α, Bisim s s := by
  tcofix cih
  exact fun s => ⟨rfl, cih _⟩

theorem bisim_symm {α : Type u} : ∀ s t : Nat → α, Bisim s t → Bisim t s := by
  tcofix cih with R hR
  guard_hyp hR : Paco.Tower _ R
  guard_hyp cih :ₛ ∀ s t : Nat → α, Bisim s t → R t s
  intro s t h
  rw [Bisim] at h
  exact ⟨h.1.symm, cih _ _ h.2⟩

/-- `tbase` on the guarded goal `f x xs` and on `x xs`; `tstep` before using `cih`. -/
example {α : Type} : ∀ s : Nat → α, Bisim s s → Bisim s s := by
  tcofix cih
  intro s h
  tbase h

example {α : Type} : ∀ s : Nat → α, Bisim s s → Bisim s s := by
  tcofix cih
  intro s h
  refine ⟨rfl, ?_⟩
  tbase bisim_refl _

example {α : Type} : ∀ s : Nat → α, Bisim s s := by
  tcofix cih
  intro s
  refine ⟨rfl, ?_⟩
  tstep
  guard_target =ₛ s (0 + 1) = s (0 + 1) ∧ φ (fun n => s (n + 1 + 1)) (fun n => s (n + 1 + 1))
  exact ⟨rfl, cih _⟩

/-- The tactics do not touch other hypotheses. -/
example (hx : (fun x : Nat => x) 1 = 1) (h φ : True) : ∀ s : Nat → Nat, Bisim s s := by
  tcofix cih
  guard_hyp hx :ₛ (fun x : Nat => x) 1 = 1
  guard_hyp h :ₛ True
  exact fun s => ⟨rfl, cih _⟩

macro "bisim_refl_tac" : tactic => `(tactic| (tcofix cih; exact fun s => ⟨rfl, cih _⟩))

example (cih : False → False) : ∀ s : Nat → Nat, Bisim s s := by
  bisim_refl_tac

/-! ## Errors -/

example (s : Nat → Nat) : True := by
  fail_if_success tcofix cih
  fail_if_success tstep
  fail_if_success tbase trivial
  trivial

example (h : Inf 0) : ∀ s : Nat → Nat, Bisim s s := by
  tcofix cih
  intro s
  refine ⟨rfl, ?_⟩
  -- `h` is about a different coinductive predicate
  fail_if_success tbase h
  exact cih _

/--
error: tcofix: the functional
  fun f s t => s 0 = t 0 ∧ f (fun n => s (n + 1)) fun n => t (n + 1)
depends on variables quantified in the goal; introduce them first
-/
#guard_msgs in
example : ∀ (α : Type) (s : Nat → α), Bisim s s := by
  tcofix cih

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
  tcofix cih

end PacoTest.Tower
