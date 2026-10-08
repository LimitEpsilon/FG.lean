import Paco

/-!
Tests: the tactics on predicates of various shapes defined with `coinductive_fixpoint`.
All goals produced by the tactics must be type-correct at `.implicit` transparency.
-/

set_option warningAsError true
set_option linter.tacticCheckInstances true

namespace PacoTest.Shapes

/-- Arity 0. -/
def Always : Prop := Always ∧ True
  coinductive_fixpoint

theorem always : Always := by
  pcofix cih
  guard_hyp cih :ₛ φ
  pfold
  exact ⟨by pleft; exact cih, trivial⟩

/-- Arity 1, the functional is a lambda. -/
def Inf (n : Nat) : Prop := Inf (n + 1)
  coinductive_fixpoint

theorem inf : ∀ n, Inf n := by
  pcofix cih
  guard_hyp cih :ₛ ∀ n, φ n
  intro n
  pfold
  pleft
  guard_target =ₛ φ (n + 1)
  exact cih _

/-- A parameter and dependent arguments. -/
def DepP (α : Type) (n : Nat) (v : Fin (n + 1)) : Prop := DepP α (n + 1) v.castSucc
  coinductive_fixpoint

theorem depP (α : Type) : ∀ n v, DepP α n v := by
  pcofix cih
  guard_hyp cih :ₛ ∀ (n : Nat) (v : Fin (n + 1)), φ n v
  intro n v
  pfold
  pleft
  exact cih _ _

/-- A fixed parameter that is not a prefix of the parameters (Lean introduces `NP.mutual`). -/
def NP (n : Nat) (x : Bool) : Prop := NP (n + 1) x
  coinductive_fixpoint

theorem np (x : Bool) : ∀ n, NP n x := by
  pcofix cih
  guard_hyp cih :ₛ ∀ n, φ n
  intro n
  pfold
  pleft
  exact cih _

/-- Definition by pattern matching. -/
def PM : Nat → Prop
  | 0 => PM 1
  | n + 1 => PM n ∧ True
  coinductive_fixpoint

theorem pm : ∀ n, PM n := by
  pcofix cih
  intro n
  pfold
  cases n with
  | zero => pleft; exact cih 1
  | succ n => exact ⟨by pleft; exact cih n, trivial⟩

universe u

/-- Universe polymorphism and higher-order arguments. -/
def Bisim {α : Type u} (s t : Nat → α) : Prop :=
  s 0 = t 0 ∧ Bisim (fun n => s (n + 1)) (fun n => t (n + 1))
  coinductive_fixpoint

theorem bisim_refl {α : Type u} : ∀ s : Nat → α, Bisim s s := by
  pcofix cih
  intro s
  pfold
  exact ⟨rfl, by pleft; apply cih⟩

theorem bisim_symm {α : Type u} : ∀ s t : Nat → α, Bisim s t → Bisim t s := by
  pcofix cih
  intro s t h
  pinit at h
  punfold at h
  obtain ⟨h0, h⟩ := h
  pclearbot at h
  pfold
  refine ⟨h0.symm, ?_⟩
  pleft
  apply cih
  -- `pinit` translates `Bisim` the same way each time
  pinit
  exact h

/-- Hypotheses mentioning the predicate itself, as in `cih : ∀ s t, Bisim s t → φ t s`. -/
theorem bisim_trans {α : Type u} :
    ∀ s t u : Nat → α, Bisim s t → Bisim t u → Bisim s u := by
  pcofix cih
  intro s t u h₁ h₂
  pinit at h₁
  pinit at h₂
  punfold at h₁
  punfold at h₂
  obtain ⟨e₁, h₁⟩ := h₁
  obtain ⟨e₂, h₂⟩ := h₂
  pclearbot at h₁
  pclearbot at h₂
  pfold
  refine ⟨e₁.trans e₂, ?_⟩
  pleft
  apply cih _ (fun n => t (n + 1))
  · pinit; exact h₁
  · pinit; exact h₂

/-- Tactic proofs inside definitions. -/
def reflexive : { s : Nat → Nat // Bisim s s } :=
  ⟨id, by
    have : ∀ s : Nat → Nat, Bisim s s := by
      pcofix cih
      intro s
      pfold
      exact ⟨rfl, by pleft; apply cih⟩
    exact this id⟩

end PacoTest.Shapes
