import FG.Basic

/-!
The proofs of `FG/Basic.lean`, redone with tower induction (`tcofix`, `tstep`, `tbase`).
-/

set_option warningAsError true
set_option linter.tacticCheckInstances true

namespace PacoTest.FlushTower

variable {τ : Type} {f g : τ → τ}

theorem base_case' : ∀ ls, Flush (f := f) (g := g) [] [] ls ls := by
  tcofix cih
  intros; apply FlushF.doEnq; intros
  tstep; apply FlushF.doF; tstep; apply FlushF.doG
  apply cih

theorem doF_case : ∀ x f0 f1 f2 fi,
  Flush (f := f) (g := g) (x :: f0) f1 f2 fi →
  Flush (f := f) (g := g) f0 (f1 ++ [f x]) f2 fi := by
  tcofix cih; intros; rename_i h; rw [Flush] at h
  cases h <;> rename_i h
  · tbase h
  · constructor; apply cih; assumption
  · apply FlushF.doEnq; intros; apply cih; apply_assumption
  · apply FlushF.doDeq; apply cih; assumption

theorem doG_case : ∀ x f0 f1 f2 fi,
  Flush (f := f) (g := g) f0 (x :: f1) f2 fi →
  Flush (f := f) (g := g) f0 f1 (f2 ++ [g x]) fi := by
  tcofix cih; intros; rename_i h; rw [Flush] at h
  cases h <;> rename_i h
  · constructor; apply_assumption; assumption
  · tbase h
  · constructor; intros; apply_assumption; apply_assumption
  · apply FlushF.doDeq; apply_assumption; assumption

theorem doEnq_case : ∀ x f0 f1 f2 fi,
  Flush (f := f) (g := g) f0 f1 f2 fi →
  Flush (f := f) (g := g) (f0 ++ [x]) f1 f2 (fi ++ [g (f x)]) := by
  tcofix cih; intros; rename_i h; rw [Flush] at h
  cases h <;> rename_i h
  · apply FlushF.doF; apply_assumption; assumption
  · apply FlushF.doG; apply_assumption; assumption
  · apply FlushF.doEnq; intros; apply_assumption; apply_assumption
  · apply FlushF.doDeq; apply_assumption; assumption

theorem doDeq_case : ∀ x f0 f1 f2 fi,
  Flush (f := f) (g := g) f0 f1 (x :: f2) (x :: fi) →
  Flush (f := f) (g := g) f0 f1 f2 fi := by
  tcofix cih; intros; rename_i h; rw [Flush] at h
  cases h <;> rename_i h
  · apply FlushF.doF; apply_assumption; assumption
  · apply FlushF.doG; apply_assumption; assumption
  · apply FlushF.doEnq; intros; apply_assumption; apply_assumption
  · tbase h

end PacoTest.FlushTower
