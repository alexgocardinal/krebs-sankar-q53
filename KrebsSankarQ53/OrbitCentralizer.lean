import KrebsSankarQ53.InvolutionOrbit

/-!
# The fixed orbit product and the square of the conjugator

When `x` does not commute with an involution `t`, the product of `t`
with its conjugate is nontrivial. Under the no-D8-section assumption,
the square of `x` centralizes their two-generator subgroup.
-/

namespace KrebsSankarQ53

theorem involutionOrbitProduct_ne_one_of_noncommute
    {G : Type*} [Group G] {x t : G}
    (ht : t * t = 1) (hne : x * t ≠ t * x) :
    involutionOrbitProduct x t ≠ 1 := by
  intro hp
  have ht' : x * t * x⁻¹ = t := by
    calc
      x * t * x⁻¹ = t * (t * (x * t * x⁻¹)) := by
        rw [← mul_assoc, ht]
        simp
      _ = t := by
        change t * involutionOrbitProduct x t = t
        rw [hp]
        simp
  have hcomm : x * t = t * x := by
    calc
      x * t = (x * t * x⁻¹) * x := by group
      _ = t * x := by rw [ht']
  exact hne hcomm

theorem square_centralizes_two_generator_subgroup_of_no_d8
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) (x t : G) (ht : t * t = 1) :
    ∀ y : Subgroup.closure ({x, t} : Set G),
      (y : G) * x ^ 2 = x ^ 2 * (y : G) := by
  have hx : x ∈ Subgroup.centralizer ({x ^ 2} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [pow_two]
    group
  have ht' : t ∈ Subgroup.centralizer ({x ^ 2} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (square_commutes_with_involution_of_no_d8 hG hno x t ht).symm
  have hgen : ({x, t} : Set G) ⊆
      Subgroup.centralizer ({x ^ 2} : Set G) := by
    intro z hz
    have hz' : z = x ∨ z = t := by simpa using hz
    rcases hz' with hzx | hzt
    · rw [hzx]
      exact hx
    · rw [hzt]
      exact ht'
  have hle : Subgroup.closure ({x, t} : Set G) ≤
      Subgroup.centralizer ({x ^ 2} : Set G) :=
    (Subgroup.closure_le _).2 hgen
  intro y
  exact (Subgroup.mem_centralizer_singleton_iff).1 (hle y.property)

end KrebsSankarQ53
