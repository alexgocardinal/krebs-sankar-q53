import KrebsSankarQ53.NoD8Involutions

/-!
# Conjugation on the involution subgroup

In a group of exponent dividing four with no D8 section, every square
commutes with every involution. Hence conjugating an involution twice by
the same group element returns it to its starting point.
-/

namespace KrebsSankarQ53

theorem square_commutes_with_involution_of_no_d8
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) (x t : G) (ht : t * t = 1) :
    x ^ 2 * t = t * x ^ 2 :=
  no_d8_section_involutions_commute hG hno (x ^ 2) t
    (square_is_involution hG x) ht

theorem conjugate_twice_involution_of_no_d8
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) (x t : G) (ht : t * t = 1) :
    x * (x * t * x⁻¹) * x⁻¹ = t := by
  have hcomm : x ^ 2 * t = t * x ^ 2 :=
    square_commutes_with_involution_of_no_d8 hG hno x t ht
  calc
    x * (x * t * x⁻¹) * x⁻¹ = x ^ 2 * t * (x ^ 2)⁻¹ := by
      simp only [pow_two]
      group
    _ = t := by rw [hcomm]; simp

theorem noncentral_involution_conjugator_order_four
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) {x t : G} (ht : t * t = 1)
    (hne : x * t ≠ t * x) :
    x ^ 2 ≠ 1 := by
  intro hx
  have hx' : x * x = 1 := by simpa only [pow_two] using hx
  exact hne (no_d8_section_involutions_commute hG hno x t hx' ht)

end KrebsSankarQ53
