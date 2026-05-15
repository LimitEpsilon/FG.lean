import Paco.Paco

variable {τ : Type} {f g : τ → τ}

inductive FlushF (Flush : List τ → List τ → List τ → List τ → Prop)
: List τ → List τ → List τ → List τ → Prop
| doF : ∀ x f0 f1 f2 fi, Flush f0 (f1 ++ [f x]) f2 fi → FlushF Flush (x :: f0) f1 f2 fi
| doG : ∀ x f0 f1 f2 fi, Flush f0 f1 (f2 ++ [g x]) fi → FlushF Flush f0 (x :: f1) f2 fi
| doEnq : ∀ f0 f1 f2 fi, (∀ x, Flush (f0 ++ [x]) f1 f2 (fi ++ [g (f x)])) → FlushF Flush f0 f1 f2 fi
| doDeq : ∀ x f0 f1 f2 fi, Flush f0 f1 f2 fi → FlushF Flush f0 f1 (x :: f2) (x :: fi)

theorem FlushF_monotone sim sim' (hsim : ∀ f0 f1 f2 fi, sim f0 f1 f2 fi → sim' f0 f1 f2 fi) :
  ∀ f0 f1 f2 fi, FlushF (f := f) (g := g) sim f0 f1 f2 fi → FlushF (f := f) (g := g) sim' f0 f1 f2 fi:= by
  intros; rename_i h
  cases h
  · constructor; apply_assumption; assumption
  · constructor; apply_assumption; assumption
  · constructor; intros; apply_assumption; apply_assumption
  · apply FlushF.doDeq; apply_assumption; assumption

def Flush (f0 f1 f2 fi : List τ) : Prop :=
  FlushF (f := f) (g := g) Flush f0 f1 f2 fi
  coinductive_fixpoint monotonicity fun sim' sim hsim =>
    FlushF_monotone sim sim' hsim

theorem base_case' : ∀ ls, Flush (f := f) (g := g) [] [] ls ls := by
  pcofix cih; intros; pfold; apply FlushF.doEnq; intros
  pright; pfold; apply FlushF.doF; pright; pfold; apply FlushF.doG
  pleft; apply cih

theorem base_case : Flush (f := f) (g := g) [] [] [] [] := base_case' _

theorem doF_case : ∀ x f0 f1 f2 fi,
  Flush (f := f) (g := g) (x :: f0) f1 f2 fi →
  Flush (f := f) (g := g) f0 (f1 ++ [f x]) f2 fi := by
  pcofix cih; intros; rename_i h; rw [Flush] at h
  cases h <;> rename_i h
  · pinit at h; pmon <;> try assumption
    ptop
  · pfold; constructor; pleft; apply cih; assumption
  · pfold; apply FlushF.doEnq; intros; pleft; apply cih; apply_assumption
  · pfold; apply FlushF.doDeq; pleft; apply cih; assumption

theorem doG_case : ∀ x f0 f1 f2 fi,
  Flush (f := f) (g := g) f0 (x :: f1) f2 fi →
  Flush (f := f) (g := g) f0 f1 (f2 ++ [g x]) fi := by
  pcofix cih; intros; rename_i h; rw [Flush] at h
  cases h <;> rename_i h
  · pfold; constructor; pleft; apply_assumption; assumption
  · pinit at h; pmon <;> try assumption
    ptop
  · pfold; constructor; intros; pleft; apply_assumption; apply_assumption
  · pfold; apply FlushF.doDeq; pleft; apply_assumption; assumption

theorem doEnq_case : ∀ x f0 f1 f2 fi,
  Flush (f := f) (g := g) f0 f1 f2 fi →
  Flush (f := f) (g := g) (f0 ++ [x]) f1 f2 (fi ++ [g (f x)]) := by
  pcofix cih; intros; rename_i h; rw [Flush] at h
  cases h <;> rename_i h
  · pfold; apply FlushF.doF; pleft; apply_assumption; assumption
  · pfold; apply FlushF.doG; pleft; apply_assumption; assumption
  · pfold; apply FlushF.doEnq; intros; pleft; apply_assumption; apply_assumption
  · pfold; apply FlushF.doDeq; pleft; apply_assumption; assumption

theorem doDeq_case : ∀ x f0 f1 f2 fi,
  Flush (f := f) (g := g) f0 f1 (x :: f2) (x :: fi) →
  Flush (f := f) (g := g) f0 f1 f2 fi := by
  pcofix cih; intros; rename_i h; rw [Flush] at h
  cases h <;> rename_i h
  · pfold; apply FlushF.doF; pleft; apply_assumption; assumption
  · pfold; apply FlushF.doG; pleft; apply_assumption; assumption
  · pfold; apply FlushF.doEnq; intros; pleft; apply_assumption; apply_assumption
  · pinit at h; pmon <;> try assumption
    ptop
