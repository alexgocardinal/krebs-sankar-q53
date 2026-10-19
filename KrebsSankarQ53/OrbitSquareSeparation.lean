import KrebsSankarQ53.OrbitLocalBundle

/-!
# The conjugator's square avoids the four-element orbit

If `x` moves an involution `t` in an exponent-four group without a
dihedral section, its square is distinct from the identity, `t`,
the conjugate of `t`, and their product. Equality with the product
would give two noncommuting involutions `t` and `t*x`, hence a D8 section.
-/

namespace KrebsSankarQ53

theorem square_ne_moved_involution
    {G : Type*} [Group G] {x t : G}
    (hne : x * t ≠ t * x) : x ^ 2 ≠ t := by
  intro heq
  apply hne
  calc
    x * t = x * x ^ 2 := by rw [heq]
    _ = x ^ 2 * x := by group
    _ = t * x := by rw [heq]

theorem square_ne_conjugate_moved_involution
    {G : Type*} [Group G] {x t : G}
    (hne : x * t ≠ t * x) : x ^ 2 ≠ x * t * x⁻¹ := by
  intro heq
  have ht : t = x ^ 2 := by
    calc
      t = x⁻¹ * (x * t * x⁻¹) * x := by group
      _ = x⁻¹ * x ^ 2 * x := by rw [← heq]
      _ = x ^ 2 := by group
  exact square_ne_moved_involution hne ht.symm

theorem square_ne_orbit_product_of_no_d8
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) {x t : G}
    (ht : t * t = 1) (hne : x * t ≠ t * x) :
    x ^ 2 ≠ involutionOrbitProduct x t := by
  intro heq
  have htx : (t * x) * (t * x) = 1 := by
    calc
      (t * x) * (t * x) = involutionOrbitProduct x t * x ^ 2 := by
        simp only [involutionOrbitProduct, pow_two]
        group
      _ = x ^ 2 * x ^ 2 := by rw [← heq]
      _ = 1 := square_is_involution hG x
  have hne' : t * (t * x) ≠ (t * x) * t := by
    intro hh
    apply hne
    calc
      x * t = (t * (t * x)) * t := by rw [← mul_assoc, ht, one_mul]
      _ = ((t * x) * t) * t := by rw [hh]
      _ = t * x := by rw [mul_assoc, ht, mul_one]
  exact hno (noncommuting_involutions_have_d8_section hG ht htx hne')

/-- The four-element orbit and the square of its conjugator are
disjoint, under the no-D8-section hypothesis. -/
theorem local_square_avoids_orbit_four
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) {x t : G}
    (ht : t * t = 1) (hne : x * t ≠ t * x) :
    x ^ 2 ≠ 1 ∧ x ^ 2 ≠ t ∧
      x ^ 2 ≠ x * t * x⁻¹ ∧
      x ^ 2 ≠ involutionOrbitProduct x t := by
  exact ⟨noncentral_involution_conjugator_order_four hG hno ht hne,
    square_ne_moved_involution hne,
    square_ne_conjugate_moved_involution hne,
    square_ne_orbit_product_of_no_d8 hG hno ht hne⟩

end KrebsSankarQ53
