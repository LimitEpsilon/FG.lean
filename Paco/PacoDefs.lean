import Paco.Lattice

/-!
# Parameterized least fixed points

For a monotone `f` on a complete lattice, `plfp f r` is the least fixed point of
`fun x => f (r ⊓ x)`, and `uplfp f r = r ⊓ plfp f r`. On predicates ordered by reverse implication,
as used by Lean's `coinductive_fixpoint`, these are the `paco` and `upaco` constructions of
Hur et al.: `plfp f ⊤ₚ` is the greatest fixed point of `f`, and the parameter `r` collects the
coinductive hypotheses accumulated so far.

All lemmas here are stated in lattice terms. The tactics in `Paco.Tactic` instantiate them at
predicate types.
-/

universe u

namespace Paco

open CompleteLattice

variable {α : Sort u} [CompleteLattice α]

/-- `f` is monotone. -/
def monotone (f : α → α) : Prop := ∀ x y, x ⊑ y → f x ⊑ f y

/-! ## Least fixed points (Knaster–Tarski) -/

/-- The least fixed point of `f`, defined as the infimum of all prefixed points. Monotonicity is
only needed to show that it is a fixed point. -/
def lfp (f : α → α) : α := inf fun x => f x ⊑ x

theorem lfp_le {f : α → α} {x : α} (h : f x ⊑ x) : lfp f ⊑ x := inf_le h

theorem le_lfp {f : α → α} {y : α} (h : ∀ x, f x ⊑ x → y ⊑ x) : y ⊑ lfp f := le_inf h

theorem lfp_prefixed {f : α → α} (hm : monotone f) : f (lfp f) ⊑ lfp f :=
  le_lfp fun _ hx => le_trans (hm _ _ (lfp_le hx)) hx

theorem lfp_fix {f : α → α} (hm : monotone f) : lfp f = f (lfp f) :=
  le_antisymm (lfp_le (hm _ _ (lfp_prefixed hm))) (lfp_prefixed hm)

/-- A prefixed point below every prefixed point is the least fixed point. -/
theorem eq_lfp {f : α → α} (hm : monotone f) {p : α} (hfix : p = f p)
    (hleast : ∀ x, f x ⊑ x → p ⊑ x) : p = lfp f :=
  le_antisymm (hleast _ (lfp_prefixed hm)) (lfp_le (hfix ▸ le_refl p))

/-! ## Parameterized fixed points -/

theorem plfp_arg_mon {f : α → α} (hm : monotone f) (r : α) : monotone fun x => f (r ⊓ x) :=
  fun _ _ h => hm _ _ (meet_mono (le_refl r) h)

set_option linter.unusedVariables false in
/-- Parameterized least fixed point: `plfp f r = lfp (fun x => f (r ⊓ x))`.
The monotonicity proof is carried along so that the tactics can unfold `plfp`. -/
def plfp (f : α → α) {hm : monotone f} (r : α) : α := lfp fun x => f (r ⊓ x)

/-- The "unfolded" parameterized fixed point `r ⊓ plfp f r`. On predicates it is pointwise
`r x₁ ⋯ xₙ ∨ plfp f r x₁ ⋯ xₙ`. -/
def uplfp (f : α → α) {hm : monotone f} (r : α) : α := r ⊓ plfp f (hm := hm) r

variable {f : α → α}

theorem plfp_unfold (hm : monotone f) (r : α) :
    plfp f (hm := hm) r = f (uplfp f (hm := hm) r) :=
  lfp_fix (plfp_arg_mon hm r)

theorem plfp_mon (hm : monotone f) : monotone (plfp f (hm := hm)) := fun _ r' h =>
  lfp_le <| le_trans (hm _ _ (meet_mono h (le_refl _)))
    (lfp_prefixed (plfp_arg_mon hm r'))

theorem uplfp_le_left (hm : monotone f) (r : α) : uplfp f (hm := hm) r ⊑ r :=
  meet_le_left _ _

theorem uplfp_le_right (hm : monotone f) (r : α) : uplfp f (hm := hm) r ⊑ plfp f (hm := hm) r :=
  meet_le_right _ _

theorem uplfp_goal (hm : monotone f) (r z : α) :
    r ⊑ z ∨ plfp f (hm := hm) r ⊑ z → uplfp f (hm := hm) r ⊑ z
  | .inl h => meet_left h
  | .inr h => meet_right h

theorem uplfp_hyp (hm : monotone f) (r z : α) :
    z ⊑ uplfp f (hm := hm) r → z ⊑ r ∧ z ⊑ plfp f (hm := hm) r :=
  meet_spec.mp

theorem uplfp_top (hm : monotone f) : uplfp f (hm := hm) ⊤ₚ = plfp f (hm := hm) ⊤ₚ :=
  top_meet _

/-- The accumulation principle, which is the basis of `pcofix`. -/
theorem plfp_acc (hm : monotone f) (l r : α)
    (obg : ∀ φ, φ ⊑ r → φ ⊑ l → plfp f (hm := hm) φ ⊑ l) : plfp f (hm := hm) r ⊑ l :=
  -- `plfp f (r ⊓ l)` is a prefixed point of `fun x => f (r ⊓ x)` below `l`
  have hl := obg (r ⊓ l) (meet_le_left r l) (meet_le_right r l)
  have hle : r ⊓ plfp f (hm := hm) (r ⊓ l) ⊑ uplfp f (hm := hm) (r ⊓ l) :=
    le_meet (le_meet (meet_le_left _ _) (meet_right hl)) (meet_le_right _ _)
  le_trans (lfp_le (le_trans (hm _ _ hle) (le_of_eq (plfp_unfold hm (r ⊓ l)).symm))) hl

/-- `plfp_acc` for a goal `Q (plfp f r)`, where `Q` is the principal down-set of some `l`.
`pcofix` instantiates `Q` with `fun p => ∀ x₁ ⋯ xₘ, p e₁ ⋯ eₙ`, so that both the coinductive
hypothesis `Q φ` and the new goal `Q (plfp f φ)` have the shape of the original goal. -/
theorem plfp_cofix (hm : monotone f) (r : α) (Q : α → Prop) (l : α)
    (hQ : ∀ p, Q p ↔ p ⊑ l) (obg : ∀ φ, φ ⊑ r → Q φ → Q (plfp f (hm := hm) φ)) :
    Q (plfp f (hm := hm) r) :=
  (hQ _).mpr <| plfp_acc hm l r fun φ hr hl => (hQ _).mp <| obg φ hr <| (hQ φ).mpr hl

theorem plfp_init (hm : monotone f) : lfp f = plfp f (hm := hm) ⊤ₚ := by
  unfold plfp
  congr
  funext x
  rw [top_meet]

/-- Identify the least fixed point of `f`, given through its fixed point equation and its
induction principle, with `plfp f ⊤ₚ`. This is how `pinit` connects definitions made with
`coinductive_fixpoint` to `plfp`. -/
theorem eq_plfp_top (hm : monotone f) {p : α} (hfix : p = f p)
    (hleast : ∀ x, f x ⊑ x → p ⊑ x) : p = plfp f (hm := hm) ⊤ₚ :=
  (eq_lfp hm hfix hleast).trans (plfp_init hm)

end Paco

export Paco (plfp uplfp)
