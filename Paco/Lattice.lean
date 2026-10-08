/-!
# Complete lattices for parameterized coinduction

This file defines the order-theoretic setting of the paco library.

We deliberately use our own `Paco.CompleteLattice` class instead of `Lean.Order.CompleteLattice`:

* Lean's `coinductive_fixpoint` orders predicates through the type synonym
  `Lean.Order.ReverseImplicationOrder`, so the lattice instance it uses for a predicate type
  `α₁ → ⋯ → αₙ → Prop` has carrier `α₁ → ⋯ → αₙ → ReverseImplicationOrder`. Terms mixing such an
  instance with `Prop`-valued predicates are only type-correct after unfolding the synonym, which
  Lean no longer does when unifying implicit and instance arguments
  (`backward.isDefEq.respectTransparency`). Our instances have carrier literally
  `α₁ → ⋯ → αₙ → Prop`, so every goal produced by the paco tactics is type-correct at `.implicit`
  transparency.
* The class contains `top` and `meet` as fields so that, on predicates, they compute to `False` and
  `∨` by unfolding instances only. This is what lets `pleft`, `pright` and `pcases` expose
  `uplfp f r x₁ ⋯ xₙ` as the disjunction `r x₁ ⋯ xₙ ∨ plfp f r x₁ ⋯ xₙ`.
* The library does not depend on the (internal and changing) lattice API of Lean core.

Following Lean's `coinductive_fixpoint`, `Prop` is ordered by *reverse* implication: `p ⊑ q` means
`q → p`. Hence the least fixed point in this lattice is the greatest fixed point with respect to
implication, `⊤ₚ` is the everywhere-false predicate and `⊓` is pointwise disjunction.
-/

universe u v

namespace Paco

/-- A complete lattice, given by its order, infima, a top element and binary meets. -/
class CompleteLattice (α : Sort u) where
  /-- The order of the lattice. On `Prop` this is reverse implication. -/
  le : α → α → Prop
  le_refl (x : α) : le x x
  le_trans {x y z : α} : le x y → le y z → le x z
  le_antisymm {x y : α} : le x y → le y x → x = y
  /-- Infimum of an arbitrary set. -/
  inf : (α → Prop) → α
  inf_le {c : α → Prop} {x : α} : c x → le (inf c) x
  le_inf {c : α → Prop} {x : α} : (∀ y, c y → le x y) → le x (inf c)
  /-- The greatest element. On `Prop` this is `False`. -/
  top : α
  le_top (x : α) : le x top
  /-- Binary meet. On `Prop` this is `∨`. -/
  meet : α → α → α
  meet_le_left (x y : α) : le (meet x y) x
  meet_le_right (x y : α) : le (meet x y) y
  le_meet {x y z : α} : le z x → le z y → le z (meet x y)

@[inherit_doc] infix:50 " ⊑ " => CompleteLattice.le
@[inherit_doc] scoped infixl:70 " ⊓ " => CompleteLattice.meet

end Paco

/-- The top element of a `Paco.CompleteLattice`; on predicates it is the everywhere-false
predicate, i.e. the empty parameter of `plfp`. -/
notation "⊤ₚ" => Paco.CompleteLattice.top

namespace Paco

/-- `Prop`, ordered by reverse implication as in Lean's `coinductive_fixpoint`. -/
instance instCompleteLatticeProp : CompleteLattice Prop where
  le p q := q → p
  le_refl _ := id
  le_trans h₁ h₂ := fun h => h₁ (h₂ h)
  le_antisymm h₁ h₂ := propext ⟨h₂, h₁⟩
  inf c := ∃ p, c p ∧ p
  inf_le hc := fun hx => ⟨_, hc, hx⟩
  le_inf h := fun ⟨p, hp, hpp⟩ => h p hp hpp
  top := False
  le_top _ := False.elim
  meet p q := p ∨ q
  meet_le_left _ _ := Or.inl
  meet_le_right _ _ := Or.inr
  le_meet h₁ h₂ := fun h => h.elim h₁ h₂

/-- The pointwise lattice on (dependent) functions. -/
instance instCompleteLatticePi {α : Sort u} {β : α → Sort v} [∀ a, CompleteLattice (β a)] :
    CompleteLattice (∀ a, β a) where
  le f g := ∀ a, f a ⊑ g a
  le_refl f a := CompleteLattice.le_refl (f a)
  le_trans h₁ h₂ a := CompleteLattice.le_trans (h₁ a) (h₂ a)
  le_antisymm h₁ h₂ := funext fun a => CompleteLattice.le_antisymm (h₁ a) (h₂ a)
  inf c a := CompleteLattice.inf fun y => ∃ f, c f ∧ f a = y
  inf_le hc _ := CompleteLattice.inf_le ⟨_, hc, rfl⟩
  le_inf h a := CompleteLattice.le_inf fun _ ⟨f, hf, hfa⟩ => hfa ▸ h f hf a
  top _ := CompleteLattice.top
  le_top f a := CompleteLattice.le_top (f a)
  meet f g a := CompleteLattice.meet (f a) (g a)
  meet_le_left f g a := CompleteLattice.meet_le_left (f a) (g a)
  meet_le_right f g a := CompleteLattice.meet_le_right (f a) (g a)
  le_meet h₁ h₂ a := CompleteLattice.le_meet (h₁ a) (h₂ a)

namespace CompleteLattice

variable {α : Sort u} [CompleteLattice α]

/-! The order on predicates unfolds pointwise to reverse implication. The tactics rely on these
definitional unfoldings, which only involve instances defined in this file. -/

theorem le_pi_iff {α : Sort u} {β : α → Sort v} [∀ a, CompleteLattice (β a)] {f g : ∀ a, β a} :
    f ⊑ g ↔ ∀ a, f a ⊑ g a := Iff.rfl

theorem le_prop_iff {p q : Prop} : p ⊑ q ↔ (q → p) := Iff.rfl

theorem meet_pi_apply {α : Sort u} {β : α → Sort v} [∀ a, CompleteLattice (β a)]
    (f g : ∀ a, β a) (a : α) : meet f g a = meet (f a) (g a) := rfl

theorem meet_prop (p q : Prop) : meet p q = (p ∨ q) := rfl

theorem top_pi_apply {α : Sort u} {β : α → Sort v} [∀ a, CompleteLattice (β a)] (x : α) :
    (top : ∀ a, β a) x = top := rfl

theorem top_prop : (top : Prop) = False := rfl

/-! ## Basic lattice facts -/

theorem top_spec (x : α) : x ⊑ ⊤ₚ := le_top x

theorem le_of_eq {x y : α} (h : x = y) : x ⊑ y := h ▸ le_refl x

theorem meet_spec {x y z : α} : z ⊑ meet x y ↔ z ⊑ x ∧ z ⊑ y :=
  ⟨fun h => ⟨le_trans h (meet_le_left x y), le_trans h (meet_le_right x y)⟩,
   fun ⟨h₁, h₂⟩ => le_meet h₁ h₂⟩

theorem meet_left {x y z : α} : x ⊑ z → meet x y ⊑ z := le_trans (meet_le_left x y)

theorem meet_right {x y z : α} : y ⊑ z → meet x y ⊑ z := le_trans (meet_le_right x y)

theorem meet_mono {x x' y y' : α} (hx : x ⊑ x') (hy : y ⊑ y') : meet x y ⊑ meet x' y' :=
  le_meet (meet_left hx) (meet_right hy)

theorem top_meet (x : α) : meet ⊤ₚ x = x :=
  le_antisymm (meet_le_right _ _) (le_meet (le_top x) (le_refl x))

theorem meet_top (x : α) : meet x ⊤ₚ = x :=
  le_antisymm (meet_le_left _ _) (le_meet (le_refl x) (le_top x))

theorem meet_comm (x y : α) : meet x y = meet y x :=
  le_antisymm (le_meet (meet_le_right x y) (meet_le_left x y))
    (le_meet (meet_le_right y x) (meet_le_left y x))

theorem meet_assoc (x y z : α) : meet (meet x y) z = meet x (meet y z) :=
  le_antisymm
    (le_meet (meet_left (meet_le_left x y))
      (le_meet (meet_left (meet_le_right x y)) (meet_le_right _ z)))
    (le_meet (le_meet (meet_le_left x _) (meet_right (meet_le_left y z)))
      (meet_right (meet_le_right y z)))

end CompleteLattice

end Paco
