import Paco

/-!
Tests: nested coinduction with parameterized tower induction.

A walk on `Nat`: states `≡ 0 (mod 4)` step to odd states, and odd states step to odd states or
back to states `≡ 0 (mod 4)`. To show that the walk never visits a state `≡ 2 (mod 4)`, we use one
coinduction for the states `≡ 0 (mod 4)` and a nested one for the odd states, which uses the outer
coinductive hypothesis.
-/

set_option warningAsError true
set_option linter.tacticCheckInstances true

namespace PacoTest.TowerNested

open Paco

def next (n : Nat) : Nat := if n % 4 = 1 then n + 2 else n + 1

def SafeF (S : Nat → Prop) (n : Nat) : Prop := n % 4 ≠ 2 ∧ S (next n)

def Safe (n : Nat) : Prop := SafeF Safe n
  coinductive_fixpoint monotonicity fun _ _ h _ ⟨h₁, h₂⟩ => ⟨h₁, h _ h₂⟩

/-! ## A modular lemma about tower elements, proven by nested coinduction -/

theorem Tower.safe_odd {hm} {x : Nat → Prop} (hx : Tower SafeF (hm := hm) x)
    (h0 : ∀ n, n % 4 = 0 → x n) : ∀ n, n % 2 = 1 → x n := by
  tcofix cih
  -- the hypothesis about `x` is now about the new tower element `φ`
  guard_hyp h0 :ₛ ∀ n, n % 4 = 0 → φ n
  guard_hyp cih :ₛ ∀ n, n % 2 = 1 → φ n
  intro n hn
  refine ⟨by omega, ?_⟩
  unfold next
  split
  · exact cih _ (by omega)
  · exact h0 _ (by omega)

theorem safe : ∀ n, n % 4 = 0 → Safe n := by
  tcofix cih with x hx
  intro n hn
  refine ⟨by omega, ?_⟩
  exact Tower.safe_odd hx cih _ (by unfold next; split <;> omega)

/-! ## Nested coinduction inside a proof -/

example : ∀ n, n % 4 = 0 → Safe n := by
  tcofix cih with x hx
  intro n hn
  refine ⟨by omega, ?_⟩
  have hodd : next n % 2 = 1 := by unfold next; split <;> omega
  generalize next n = m at hodd
  revert m
  -- nested coinduction for the odd states
  tcofix cih' with y hy
  guard_hyp hy : Tower SafeF y
  -- the outer coinductive hypothesis is transported to `y`
  guard_hyp cih :ₛ ∀ n, n % 4 = 0 → y n
  guard_hyp cih' :ₛ ∀ m, m % 2 = 1 → y m
  intro m hm
  refine ⟨by omega, ?_⟩
  unfold next
  split
  · exact cih' _ (by omega)
  · exact cih _ (by omega)

/-- The inclusion of the outer tower element is available (inaccessible by default), and the
default name of the new tower element avoids the existing `φ`. -/
example : ∀ n, n % 4 = 0 → Safe n := by
  tcofix cih
  intro n hn
  refine ⟨by omega, ?_⟩
  have hodd : next n % 2 = 1 := by unfold next; split <;> omega
  generalize next n = m at hodd
  revert m
  tcofix cih'
  rename_i _ hle
  guard_hyp hle :ₛ ∀ n, φ n → φ_1 n
  intro m hm
  refine ⟨by omega, ?_⟩
  unfold next
  split
  · exact cih' _ (by omega)
  · -- `tstep` and `tbase` act on the innermost tower element
    tstep
    exact ⟨by omega, cih' _ (by unfold next; split <;> omega)⟩

/-- Hypotheses in which the outer tower element occurs elsewhere are left alone. -/
example : ∀ n, n % 4 = 0 → Safe n := by
  tcofix cih with x hx
  intro n hn
  have hstep : ∀ k, x k → x (k + 0) := fun k h => h
  refine ⟨by omega, ?_⟩
  have hodd : next n % 2 = 1 := by unfold next; split <;> omega
  generalize next n = m at hodd
  revert m
  tcofix cih' with y hy
  guard_hyp hstep :ₛ ∀ k, x k → x (k + 0)
  intro m hm
  refine ⟨by omega, ?_⟩
  unfold next
  split
  · exact cih' _ (by omega)
  · exact cih _ (by omega)

end PacoTest.TowerNested
