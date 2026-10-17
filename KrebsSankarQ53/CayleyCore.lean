import Mathlib

/-!
# General Cayley-graph coloring lemmas

These lemmas apply to arbitrary groups, including infinite groups. They are
building blocks for the section-lifting proof, not the full classification.
-/

namespace KrebsSankarQ53

/-- Right Cayley adjacency for a connection set `S`. -/
def rightCayleyAdj {G : Type*} [Group G] (S : Set G) (x y : G) : Prop :=
  ∃ s ∈ S, y = x * s

/-- A coloring separates the endpoints of every Cayley edge. -/
def CayleyProperColoring {G : Type*} [Group G] (S : Set G)
    {n : Nat} (c : G → Fin n) : Prop :=
  ∀ x y, rightCayleyAdj S x y → c x ≠ c y

/-- A homomorphism sends edges to edges if it sends generators to generators. -/
theorem rightCayleyAdj_map {G H : Type*} [Group G] [Group H]
    (f : G →* H) (S : Set G) (T : Set H)
    (hS : ∀ s ∈ S, f s ∈ T) {x y : G}
    (hxy : rightCayleyAdj S x y) :
    rightCayleyAdj T (f x) (f y) := by
  rcases hxy with ⟨s, hs, rfl⟩
  exact ⟨f s, hS s hs, map_mul f x s⟩

/-- A proper coloring pulls back along a homomorphism preserving the edges. -/
theorem cayleyColor_pullback {G H : Type*} [Group G] [Group H]
    (f : G →* H) (S : Set G) (T : Set H) (n : Nat)
    (hS : ∀ s ∈ S, f s ∈ T) (c : H → Fin n)
    (hc : CayleyProperColoring T c) :
    CayleyProperColoring S (fun x => c (f x)) := by
  intro x y hxy
  exact hc (f x) (f y) (rightCayleyAdj_map f S T hS hxy)

private theorem five_colors_impossible :
    ¬ ∃ a b c d e : Fin 2,
      a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ e ∧ e ≠ a := by
  decide

/-- An explicitly exhibited five-cycle makes a two-coloring impossible. -/
theorem no_two_of_five_cycle {G : Type*} [Group G] (S : Set G)
    (v₀ v₁ v₂ v₃ v₄ : G)
    (h₀ : rightCayleyAdj S v₀ v₁)
    (h₁ : rightCayleyAdj S v₁ v₂)
    (h₂ : rightCayleyAdj S v₂ v₃)
    (h₃ : rightCayleyAdj S v₃ v₄)
    (h₄ : rightCayleyAdj S v₄ v₀) :
    ¬ ∃ c : G → Fin 2, CayleyProperColoring S c := by
  rintro ⟨c, hc⟩
  exact five_colors_impossible ⟨c v₀, c v₁, c v₂, c v₃, c v₄,
    hc v₀ v₁ h₀, hc v₁ v₂ h₁, hc v₂ v₃ h₂,
    hc v₃ v₄ h₃, hc v₄ v₀ h₄⟩

end KrebsSankarQ53
