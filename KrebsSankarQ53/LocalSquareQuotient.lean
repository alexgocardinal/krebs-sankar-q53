import KrebsSankarQ53.LocalSquareSubgroup

/-!
# Two noncommuting involutions in the local square quotient

The quotient construction turns the conjugator into an involution.
The original involution survives, and their commutator is excluded
from the square subgroup by the orbit separation lemmas.
-/

namespace KrebsSankarQ53

theorem exponentFour_quotient
    {K : Type*} [Group K] (hK : ExponentFour K)
    (N : Subgroup K) [N.Normal] : ExponentFour (K ⧸ N) := by
  intro z
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N z
  let q : K →* K ⧸ N := QuotientGroup.mk' N
  calc
    (q y) ^ 4 = q (y ^ 4) := (map_pow q y 4).symm
    _ = 1 := by rw [hK y, map_one]

theorem quotient_noncommuting_involutions
    {K : Type*} [Group K] (N : Subgroup K) [N.Normal]
    (a b : K) (ha : a * a ∈ N) (hb : b * b ∈ N)
    (hne : (a * b * a⁻¹) / b ∉ N) :
    ∃ A B : K ⧸ N, A * A = 1 ∧ B * B = 1 ∧ A * B ≠ B * A := by
  let q : K →* K ⧸ N := QuotientGroup.mk' N
  refine ⟨q a, q b, ?_, ?_, ?_⟩
  · calc
      q a * q a = q (a * a) := (map_mul q a a).symm
      _ = 1 := by
        simpa only [q, QuotientGroup.mk'_apply] using
          (QuotientGroup.eq_one_iff (a * a)).2 ha
  · calc
      q b * q b = q (b * b) := (map_mul q b b).symm
      _ = 1 := by
        simpa only [q, QuotientGroup.mk'_apply] using
          (QuotientGroup.eq_one_iff (b * b)).2 hb
  · intro hcomm
    have heq : q (a * b * a⁻¹) = q b := by
      calc
        q (a * b * a⁻¹) = q a * q b * (q a)⁻¹ := by simp [map_mul]
        _ = q b := by rw [hcomm]; group
    have hmem : (a * b * a⁻¹) / b ∈ N :=
      QuotientGroup.eq_iff_div_mem.mp (by
        simpa only [q, QuotientGroup.mk'_apply] using heq)
    exact hne hmem

theorem local_square_quotient_noncommuting_involutions
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) {x t : G}
    (ht : t * t = 1) (hne : x * t ≠ t * x)
    (W : Subgroup (Subgroup.closure ({x, t} : Set G))) [W.Normal]
    (hW : W = (squarePairSubgroup (x ^ 2)
      (square_is_involution hG x)).subgroupOf
        (Subgroup.closure ({x, t} : Set G))) :
    ∃ A B : (Subgroup.closure ({x, t} : Set G)) ⧸ W,
      A * A = 1 ∧ B * B = 1 ∧ A * B ≠ B * A := by
  let H : Subgroup G := Subgroup.closure ({x, t} : Set G)
  have hx : x ∈ H := Subgroup.subset_closure (by simp)
  have htH : t ∈ H := Subgroup.subset_closure (by simp)
  let a : H := ⟨x, hx⟩
  let b : H := ⟨t, htH⟩
  have haW : a * a ∈ W := by
    rw [hW]
    change x * x = 1 ∨ x * x = x ^ 2
    exact Or.inr (pow_two x).symm
  have hbW : b * b ∈ W := by
    rw [hW]
    change t * t = 1 ∨ t * t = x ^ 2
    exact Or.inl ht
  have hcommG : (x * t * x⁻¹) / t = involutionOrbitProduct x t := by
    calc
      (x * t * x⁻¹) / t = (x * t * x⁻¹) * t := by
        rw [div_eq_mul_inv, involution_inv ht]
      _ = t * (x * t * x⁻¹) :=
        (local_orbit_involutions_commute hG hno x t ht).symm
      _ = involutionOrbitProduct x t := rfl
  have hcommW : (a * b * a⁻¹) / b ∉ W := by
    intro hm
    rw [hW] at hm
    change (x * t * x⁻¹) / t = 1 ∨
      (x * t * x⁻¹) / t = x ^ 2 at hm
    rw [hcommG] at hm
    rcases hm with hm | hm
    · exact (involutionOrbitProduct_ne_one_of_noncommute ht hne) hm
    · exact (square_ne_orbit_product_of_no_d8 hG hno ht hne) hm.symm
  exact quotient_noncommuting_involutions W a b haW hbW hcommW

end KrebsSankarQ53
