import KrebsSankarQ53.NoncommutingWitness
import KrebsSankarQ53.InvolutionSubgroup

/-!
# First step toward the reverse classification

If an exponent-four group has no section isomorphic to D8, any two
involutions commute. The square-one elements therefore form the normal
abelian subgroup constructed earlier.
-/

namespace KrebsSankarQ53

/-- A D8 section consists of a subgroup and a surjective homomorphism
from that subgroup to the concrete eight-element dihedral group. -/
def HasD8Section (G : Type*) [Group G] : Prop :=
  ∃ (H : Subgroup G) (f : H →* D8), Function.Surjective f

theorem noncommuting_involutions_have_d8_section
    {G : Type*} [Group G] (hG : ExponentFour G)
    {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hne : a * b ≠ b * a) : HasD8Section G := by
  let H : Subgroup G := Subgroup.closure ({a, b} : Set G)
  let f : H →* D8 := d8GeneratedSection hG ha hb hne
  exact ⟨H, f, d8GeneratedSection_surjective hG ha hb hne⟩

theorem no_d8_section_involutions_commute
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) (a b : G)
    (ha : a * a = 1) (hb : b * b = 1) :
    a * b = b * a := by
  by_contra hne
  exact hno (noncommuting_involutions_have_d8_section hG ha hb hne)

/-- The square-one elements form an abelian, conjugation-invariant
subgroup whenever there is no D8 section. -/
theorem no_d8_section_involution_subgroup
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) :
    ∃ T : Subgroup G,
      (∀ x : G, x ∈ T ↔ x * x = 1) ∧
      (∀ x y : T, x * y = y * x) ∧
      (∀ (g : G) (x : T), g * (x : G) * g⁻¹ ∈ T) := by
  let hcomm : ∀ a b : G, a * a = 1 → b * b = 1 → a * b = b * a :=
    no_d8_section_involutions_commute hG hno
  refine ⟨involutionSubgroup hcomm, ?_, ?_, ?_⟩
  · intro x
    rfl
  · exact involutionSubgroup_mul_comm hcomm
  · exact involutionSubgroup_conj_mem hcomm

end KrebsSankarQ53
