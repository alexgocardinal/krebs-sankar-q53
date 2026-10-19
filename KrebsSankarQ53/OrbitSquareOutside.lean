import KrebsSankarQ53.OrbitKleinSubgroup

/-!
# A central square outside the local four-element subgroup

Under the no-D8-section assumption, if `x` moves an involution `t`,
its square is a nontrivial involution in the generated subgroup,
centralizes that subgroup, and lies outside the four-element orbit
subgroup. This is the input for the order-sixteen local argument.
-/

namespace KrebsSankarQ53

theorem square_not_mem_orbit_klein
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) {x t : G}
    (ht : t * t = 1) (hne : x * t ≠ t * x) :
    x ^ 2 ∉ orbitKleinSubgroup t (x * t * x⁻¹) ht
      (conjugate_involution ht)
      (local_orbit_involutions_commute hG hno x t ht) := by
  intro hw
  change x ^ 2 = 1 ∨ x ^ 2 = t ∨
    x ^ 2 = x * t * x⁻¹ ∨
    x ^ 2 = t * (x * t * x⁻¹) at hw
  have hsep := local_square_avoids_orbit_four hG hno ht hne
  rcases hw with h | h | h | h
  · exact hsep.1 h
  · exact hsep.2.1 h
  · exact hsep.2.2.1 h
  · exact hsep.2.2.2 h

/-- Conjugation by the moving element swaps the two orbit involutions
and fixes their product. -/
theorem orbit_klein_stable_under_conjugator
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) (x t : G) (ht : t * t = 1)
    (a : G)
    (ha : a ∈ orbitKleinSubgroup t (x * t * x⁻¹) ht
      (conjugate_involution ht)
      (local_orbit_involutions_commute hG hno x t ht)) :
    x * a * x⁻¹ ∈ orbitKleinSubgroup t (x * t * x⁻¹) ht
      (conjugate_involution ht)
      (local_orbit_involutions_commute hG hno x t ht) := by
  change a = 1 ∨ a = t ∨ a = x * t * x⁻¹ ∨
    a = t * (x * t * x⁻¹) at ha
  change x * a * x⁻¹ = 1 ∨ x * a * x⁻¹ = t ∨
    x * a * x⁻¹ = x * t * x⁻¹ ∨
    x * a * x⁻¹ = t * (x * t * x⁻¹)
  rcases ha with ha | ha | ha | ha
  · rw [ha]
    exact Or.inl (by group)
  · rw [ha]
    exact Or.inr (Or.inr (Or.inl rfl))
  · rw [ha, conjugate_twice_involution_of_no_d8 hG hno x t ht]
    exact Or.inr (Or.inl rfl)
  · rw [ha]
    have hcomm := involutionOrbitProduct_commutes_with_conjugator hG hno x t ht
    have hfix : x * (t * (x * t * x⁻¹)) * x⁻¹ =
        t * (x * t * x⁻¹) := by
      change x * involutionOrbitProduct x t * x⁻¹ =
        involutionOrbitProduct x t
      rw [hcomm]
      group
    exact Or.inr (Or.inr (Or.inr hfix))

/-- The finite local subgroup, its position inside the two-generator
subgroup, and the central square outside it, in a single statement. -/
theorem orbit_klein_with_external_central_square
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) {x t : G}
    (ht : t * t = 1) (hne : x * t ≠ t * x) :
    ∃ A : Subgroup G,
      Nat.card A = 4 ∧
      A ≤ Subgroup.closure ({x, t} : Set G) ∧
      x ^ 2 ∈ Subgroup.closure ({x, t} : Set G) ∧
      x ^ 2 ∉ A ∧ x ^ 2 * x ^ 2 = 1 ∧
      (∀ y : Subgroup.closure ({x, t} : Set G),
        (y : G) * x ^ 2 = x ^ 2 * (y : G)) := by
  let A : Subgroup G := orbitKleinSubgroup t (x * t * x⁻¹) ht
    (conjugate_involution ht)
    (local_orbit_involutions_commute hG hno x t ht)
  refine ⟨A, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact orbit_klein_card_four hG hno ht hne
  · exact orbit_klein_mem_closure_pair hG hno x t ht
  · exact square_mem_closure_pair x t
  · exact square_not_mem_orbit_klein hG hno ht hne
  · exact square_is_involution hG x
  · exact square_centralizes_two_generator_subgroup_of_no_d8 hG hno x t ht

end KrebsSankarQ53
