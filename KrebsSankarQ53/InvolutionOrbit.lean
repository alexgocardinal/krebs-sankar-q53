import KrebsSankarQ53.InvolutionConjugation

/-!
# A two-element conjugation orbit

Under the no-D8-section hypothesis, conjugation by `x` takes an
involution `t` to another involution and takes that conjugate back to
`t`. Their product is fixed by conjugation by `x`.
-/

namespace KrebsSankarQ53

def involutionOrbitProduct {G : Type*} [Group G] (x t : G) : G :=
  t * (x * t * x⁻¹)

theorem involutionOrbitProduct_involution
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) (x t : G) (ht : t * t = 1) :
    involutionOrbitProduct x t * involutionOrbitProduct x t = 1 := by
  have ht' : (x * t * x⁻¹) * (x * t * x⁻¹) = 1 :=
    conjugate_involution ht
  let hcomm : ∀ a b : G, a * a = 1 → b * b = 1 → a * b = b * a :=
    no_d8_section_involutions_commute hG hno
  have hmem : t * (x * t * x⁻¹) ∈ involutionSubgroup hcomm :=
    (involutionSubgroup hcomm).mul_mem ht ht'
  exact hmem

theorem involutionOrbitProduct_commutes_with_conjugator
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) (x t : G) (ht : t * t = 1) :
    x * involutionOrbitProduct x t =
      involutionOrbitProduct x t * x := by
  have ht' : (x * t * x⁻¹) * (x * t * x⁻¹) = 1 :=
    conjugate_involution ht
  have hcomm : t * (x * t * x⁻¹) = (x * t * x⁻¹) * t :=
    no_d8_section_involutions_commute hG hno t
      (x * t * x⁻¹) ht ht'
  have hfix : x * involutionOrbitProduct x t * x⁻¹ =
      involutionOrbitProduct x t := by
    calc
      x * involutionOrbitProduct x t * x⁻¹ =
          (x * t * x⁻¹) * (x * (x * t * x⁻¹) * x⁻¹) := by
            simp only [involutionOrbitProduct]
            group
      _ = (x * t * x⁻¹) * t := by
        rw [conjugate_twice_involution_of_no_d8 hG hno x t ht]
      _ = involutionOrbitProduct x t := hcomm.symm
  calc
    x * involutionOrbitProduct x t =
        (x * involutionOrbitProduct x t * x⁻¹) * x := by group
    _ = involutionOrbitProduct x t * x := by rw [hfix]

end KrebsSankarQ53
