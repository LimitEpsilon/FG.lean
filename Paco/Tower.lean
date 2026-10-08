import Paco.PacoDefs

/-!
# Tower induction

Following Schäfer and Smolka, *Tower Induction and Up-To Techniques for CCS with Fixed Points*
(RAMiCS 2017), the *tower* of `f` is the least set containing `f x` for each of its elements `x` and
closed under arbitrary suprema. Its greatest element is `lfp f`, and induction on the tower
(`tower_cofix`) is a coinduction principle in which the coinductive hypothesis is about an arbitrary
tower element `x`. Because `x` is a tower element, everything proven about all tower elements is
available in the proof, in particular `x ⊑ f x` (`Tower.le_step`), `x ⊑ lfp f` (`Tower.le_lfp`)
and closure under every up-to function satisfying `Tower.closed`.

Recall that the order of this library is reverse implication on predicates (as for Lean's
`coinductive_fixpoint`), so `lfp f` is the greatest fixed point with respect to implication and
suprema are intersections. Pointwise, for a tower element `x` of the functional `f` of a coinductive
predicate `C`:

* `Tower.le_step`: `f x xs → x xs` (continue the proof by unfolding once more),
* `Tower.le_lfp`: `C xs → x xs` (use a proof of `C`),
* `Tower.closed`: `g x xs → x xs` for up-to functions `g` (up-to techniques).

Parameterized tower induction (`Tower.cofix`) proves a statement about a given tower element `x`
by induction over the tower elements containing `x`; this is nested coinduction.
-/

universe u

namespace Paco

open CompleteLattice

variable {α : Sort u} [CompleteLattice α]

/-- The supremum of `c`, the infimum of its upper bounds. On predicates it is the intersection. -/
def sup (c : α → Prop) : α := inf fun z => ∀ y, c y → y ⊑ z

theorem le_sup {c : α → Prop} {y : α} (h : c y) : y ⊑ sup c := le_inf fun _ hz => hz y h

theorem sup_le {c : α → Prop} {z : α} (h : ∀ y, c y → y ⊑ z) : sup c ⊑ z := inf_le h

set_option linter.unusedVariables false in
/-- The tower of `f`: the least set closed under `f` and arbitrary suprema. As for `plfp`, the
monotonicity proof is carried along for the benefit of the tactics. -/
inductive Tower (f : α → α) {hm : monotone f} : α → Prop
  | step {x : α} : Tower f x → Tower f (f x)
  | sup (c : α → Prop) : (∀ y, c y → Tower f y) → Tower f (sup c)

variable {f : α → α} {hm : monotone f}

namespace Tower

/-- Tower elements are post-fixed points: pointwise, `f x xs → x xs`. -/
theorem le_step {x : α} (hx : Tower f (hm := hm) x) : x ⊑ f x := by
  induction hx with
  | step _ ih => exact hm _ _ ih
  | sup c _ ih => exact sup_le fun y hy => le_trans (ih y hy) (hm _ _ (le_sup hy))

/-- Tower elements are below the least fixed point: pointwise, `C xs → x xs`. -/
theorem le_lfp {x : α} (hx : Tower f (hm := hm) x) : x ⊑ lfp f := by
  induction hx with
  | step _ ih => exact le_trans (hm _ _ ih) (le_of_eq (lfp_fix hm).symm)
  | sup c _ ih => exact sup_le ih

/-- Up-to lemma (Schäfer and Smolka, Lemma 8). To show that every tower element is closed under a
monotone `g` (pointwise, `g x xs → x xs`), it suffices to show that `f x` is closed under `g` for
every tower element `x` that is closed under `g`. Every function compatible with `f` satisfies
this condition. -/
theorem closed {g : α → α} (hg : monotone g)
    (h : ∀ x, Tower f (hm := hm) x → x ⊑ g x → f x ⊑ g (f x)) {x : α}
    (hx : Tower f (hm := hm) x) : x ⊑ g x := by
  induction hx with
  | step hx ih => exact h _ hx ih
  | sup c _ ih => exact sup_le fun y hy => le_trans (ih y hy) (hg _ _ (le_sup hy))

/-- Parameterized tower induction (Schäfer and Smolka, Lemma 25), the basis of nested coinduction.
To show `Q x` for a tower element `x`, where `Q` is the principal down-set of some `l`, it suffices
to show `Q (f z)` for every tower element `z ⊑ x` satisfying `Q z`. Pointwise, `z ⊑ x` says that
`z` contains `x`, so everything known about `x` (such as an outer coinductive hypothesis) also
holds for `z`. -/
theorem cofix {x : α} (hx : Tower f (hm := hm) x) (Q : α → Prop) (l : α) (hQ : ∀ p, Q p ↔ p ⊑ l)
    (step : ∀ z, Tower f (hm := hm) z → z ⊑ x → Q z → Q (f z)) : Q x := by
  have key : ∀ z, Tower f (hm := hm) z → z ⊑ x → z ⊑ l := by
    intro z hz
    induction hz with
    | step hz ih =>
      intro hle
      have hzx := le_trans hz.le_step hle
      exact (hQ _).mp (step _ hz hzx ((hQ _).mpr (ih hzx)))
    | sup c _ ih => exact fun hle => sup_le fun y hy => ih y hy (le_trans (le_sup hy) hle)
  exact (hQ _).mpr (key x hx (le_refl x))

end Tower

/-- Tower induction for a goal `Q (lfp f)`, where `Q` is the principal down-set of some `l`. The
tactic `tcofix` instantiates `Q` with `fun p => ∀ x₁ ⋯ xₘ, p e₁ ⋯ eₙ`, so that the coinductive
hypothesis is `Q x` and the goal is `Q (f x)` for an arbitrary tower element `x`.
Monotonicity of `f` is not needed. -/
theorem tower_cofix (hm : monotone f) (Q : α → Prop) (l : α) (hQ : ∀ p, Q p ↔ p ⊑ l)
    (step : ∀ x, Tower f (hm := hm) x → Q x → Q (f x)) : Q (lfp f) := by
  have hT : ∀ x, Tower f (hm := hm) x → x ⊑ l := by
    intro x hx
    induction hx with
    | step hx ih => exact (hQ _).mp (step _ hx ((hQ _).mpr ih))
    | sup c _ ih => exact sup_le ih
  -- the supremum of the tower is a tower element and a prefixed point of `f`
  have hs : Tower f (hm := hm) (sup (Tower f (hm := hm))) := .sup _ fun _ hy => hy
  exact (hQ _).mpr <| le_trans (lfp_le (le_sup (Tower.step hs))) (hT _ hs)

end Paco
