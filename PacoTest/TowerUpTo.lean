import Paco

/-!
Tests: up-to techniques with tower induction.

Stream terms with pointwise addition. We show `nats ⊞ nats ∼ evens`. The smallest bisimulation
containing this pair is infinite, but the pair alone is a bisimulation up to `⊞`-contexts and
bisimilarity. With tower induction, both up-to techniques are lemmas about tower elements.
-/

set_option warningAsError true
set_option linter.tacticCheckInstances true

namespace PacoTest.TowerUpTo

open Paco

inductive STerm where
  | nats | ones | twos | evens
  | add (a b : STerm)

open STerm

infixl:65 " ⊞ " => STerm.add

def hd : STerm → Nat
  | nats => 0
  | ones => 1
  | twos => 2
  | evens => 0
  | .add a b => hd a + hd b

def tl : STerm → STerm
  | nats => nats ⊞ ones
  | ones => ones
  | twos => twos
  | evens => evens ⊞ twos
  | .add a b => tl a ⊞ tl b

def BisimF (R : STerm → STerm → Prop) (s t : STerm) : Prop := hd s = hd t ∧ R (tl s) (tl t)

def Bisim (s t : STerm) : Prop := BisimF Bisim s t
  coinductive_fixpoint monotonicity fun _ _ h _ _ ⟨e, hr⟩ => ⟨e, h _ _ hr⟩

infix:50 " ∼ " => Bisim

/-! ## Plain coinduction (no up-to needed) -/

theorem ones_add_ones : ones ⊞ ones ∼ twos := by
  tcofix cih
  exact ⟨rfl, cih⟩

theorem medial : ∀ a b c d, (a ⊞ b) ⊞ (c ⊞ d) ∼ (a ⊞ c) ⊞ (b ⊞ d) := by
  tcofix cih
  intro a b c d
  exact ⟨Nat.add_add_add_comm .., cih ..⟩

/-! ## Up-to techniques: closure properties of tower elements -/

variable {hm : monotone BisimF} {x : STerm → STerm → Prop}

/-- Up to context: tower elements are closed under `⊞`. -/
theorem Tower.add (hx : Tower BisimF (hm := hm) x) {a b c d} (h₁ : x a b) (h₂ : x c d) :
    x (a ⊞ c) (b ⊞ d) := by
  -- the closure under `⊞`, as an up-to function
  let g (R : STerm → STerm → Prop) (s t : STerm) : Prop :=
    ∃ a b c d, s = a ⊞ c ∧ t = b ⊞ d ∧ R a b ∧ R c d
  have := hx.closed (g := g) (fun _ _ hR _ _ ⟨a, b, c, d, hs, ht, h₁, h₂⟩ =>
      ⟨a, b, c, d, hs, ht, hR _ _ h₁, hR _ _ h₂⟩)
    (fun x _ hclosed _ _ ⟨a, b, c, d, hs, ht, ⟨e₁, h₁⟩, ⟨e₂, h₂⟩⟩ => by
      subst hs ht
      exact ⟨by simp only [hd, e₁, e₂], hclosed _ _ ⟨_, _, _, _, rfl, rfl, h₁, h₂⟩⟩)
  exact this _ _ ⟨a, b, c, d, rfl, rfl, h₁, h₂⟩

/-- Up to bisimilarity: tower elements are closed under `∼` on the left. -/
theorem Tower.bisim_left (hx : Tower BisimF (hm := hm) x) {s s' t} (h₁ : s ∼ s') (h₂ : x s' t) :
    x s t := by
  let g (R : STerm → STerm → Prop) (s t : STerm) : Prop := ∃ s', s ∼ s' ∧ R s' t
  have := hx.closed (g := g) (fun _ _ hR _ _ ⟨s', h₁, h₂⟩ => ⟨s', h₁, hR _ _ h₂⟩)
    (fun x _ hclosed _ _ ⟨s', h₁, e, h₂⟩ => by
      rw [Bisim] at h₁
      exact ⟨h₁.1.trans e, hclosed _ _ ⟨_, h₁.2, h₂⟩⟩)
  exact this _ _ ⟨s', h₁, h₂⟩

/-! ## The main proof: a one-pair bisimulation up to context and bisimilarity -/

theorem nats_add_nats : nats ⊞ nats ∼ evens := by
  tcofix cih with x hx
  refine ⟨rfl, ?_⟩
  -- goal: `x ((nats ⊞ ones) ⊞ (nats ⊞ ones)) (evens ⊞ twos)`
  refine Tower.bisim_left hx (medial ..) ?_
  -- goal: `x ((nats ⊞ nats) ⊞ (ones ⊞ ones)) (evens ⊞ twos)`
  exact Tower.add hx cih (by tbase ones_add_ones)

end PacoTest.TowerUpTo
