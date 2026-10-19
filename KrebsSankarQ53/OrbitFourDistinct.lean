import KrebsSankarQ53.OrbitCenters

/-!
# Four distinct elements in a moved involution orbit

If `x` moves an involution `t`, the identity, `t`, its conjugate by
`x`, and their product are pairwise distinct. The latter three are
involutions when the group has exponent dividing four and no D8 section.
-/

namespace KrebsSankarQ53

theorem moved_involution_ne_one
    {G : Type*} [Group G] {x t : G}
    (hne : x * t ≠ t * x) : t ≠ 1 := by
  intro ht
  apply hne
  rw [ht]
  simp

theorem moved_involution_conjugate_ne_self
    {G : Type*} [Group G] {x t : G}
    (hne : x * t ≠ t * x) : x * t * x⁻¹ ≠ t := by
  intro heq
  apply hne
  calc
    x * t = (x * t * x⁻¹) * x := by group
    _ = t * x := by rw [heq]

theorem moved_involution_conjugate_ne_one
    {G : Type*} [Group G] {x t : G}
    (hne : x * t ≠ t * x) : x * t * x⁻¹ ≠ 1 := by
  intro heq
  have ht : t = 1 := by
    calc
      t = x⁻¹ * (x * t * x⁻¹) * x := by group
      _ = 1 := by rw [heq]; simp
  exact moved_involution_ne_one hne ht

theorem orbit_product_ne_first_of_noncommute
    {G : Type*} [Group G] {x t : G}
    (hne : x * t ≠ t * x) : involutionOrbitProduct x t ≠ t := by
  intro heq
  have hconj : x * t * x⁻¹ = 1 := by
    have h : t * (x * t * x⁻¹) = t * 1 := by
      simpa only [involutionOrbitProduct, mul_one] using heq
    exact mul_left_cancel h
  exact moved_involution_conjugate_ne_one hne hconj

theorem orbit_product_ne_second_of_noncommute
    {G : Type*} [Group G] {x t : G}
    (hne : x * t ≠ t * x) :
    involutionOrbitProduct x t ≠ x * t * x⁻¹ := by
  intro heq
  have ht : t = 1 := by
    have h : t * (x * t * x⁻¹) = 1 * (x * t * x⁻¹) := by
      simpa only [involutionOrbitProduct, one_mul] using heq
    exact mul_right_cancel h
  exact moved_involution_ne_one hne ht

/-- The four elements used in the local Klein-four construction
are pairwise distinct. -/
theorem moved_involution_four_distinct
    {G : Type*} [Group G] {x t : G} (ht : t * t = 1)
    (hne : x * t ≠ t * x) :
    t ≠ 1 ∧ x * t * x⁻¹ ≠ 1 ∧ x * t * x⁻¹ ≠ t ∧
      involutionOrbitProduct x t ≠ 1 ∧
      involutionOrbitProduct x t ≠ t ∧
      involutionOrbitProduct x t ≠ x * t * x⁻¹ := by
  exact ⟨moved_involution_ne_one hne,
    moved_involution_conjugate_ne_one hne,
    moved_involution_conjugate_ne_self hne,
    involutionOrbitProduct_ne_one_of_noncommute ht hne,
    orbit_product_ne_first_of_noncommute hne,
    orbit_product_ne_second_of_noncommute hne⟩

end KrebsSankarQ53
