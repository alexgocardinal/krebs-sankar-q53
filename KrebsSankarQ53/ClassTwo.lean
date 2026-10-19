import KrebsSankarQ53.CentralSquares

/-!
# Centrality of commutators

Central squares give a direct expression for a commutator as a
product of three central squares. This proves the class-two part
of the structural argument without a finiteness assumption.
-/

namespace KrebsSankarQ53

def commutatorTerm {G : Type*} [Group G] (x y : G) : G :=
  x * y * x⁻¹ * y⁻¹

theorem commutatorTerm_eq_squares
    {G : Type*} [Group G] (x y : G)
    (hxy : x ^ 2 * y = y * x ^ 2) :
    commutatorTerm x y =
      (x * y) ^ 2 * (x ^ 2 * y ^ 2)⁻¹ := by
  have hswap : y⁻¹ * x ^ 2 = x ^ 2 * y⁻¹ :=
    ((show Commute (x ^ 2) y from hxy).inv_right).eq.symm
  have hprod : commutatorTerm x y * (x ^ 2 * y ^ 2) =
      (x * y) ^ 2 := by
    dsimp [commutatorTerm]
    calc
      x * y * x⁻¹ * y⁻¹ * (x ^ 2 * y ^ 2) =
          x * y * x⁻¹ * (y⁻¹ * x ^ 2) * y ^ 2 := by group
      _ = x * y * x⁻¹ * (x ^ 2 * y⁻¹) * y ^ 2 := by rw [hswap]
      _ = (x * y) ^ 2 := by simp only [pow_two]; group
  calc
    commutatorTerm x y =
        (commutatorTerm x y * (x ^ 2 * y ^ 2)) *
          (x ^ 2 * y ^ 2)⁻¹ := by group
    _ = (x * y) ^ 2 * (x ^ 2 * y ^ 2)⁻¹ := by rw [hprod]

theorem no_d8_section_commutators_central
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) (x y z : G) :
    commutatorTerm x y * z = z * commutatorTerm x y := by
  have hxy : x ^ 2 * y = y * x ^ 2 :=
    no_d8_section_squares_central hG hno x y
  have hfirst : Commute ((x * y) ^ 2) z :=
    no_d8_section_squares_central hG hno (x * y) z
  have hsecond : Commute (x ^ 2 * y ^ 2) z :=
    (show Commute (x ^ 2) z from
      no_d8_section_squares_central hG hno x z).mul_left
      (show Commute (y ^ 2) z from
        no_d8_section_squares_central hG hno y z)
  rw [commutatorTerm_eq_squares x y hxy]
  exact (hfirst.mul_left hsecond.inv_left).eq

end KrebsSankarQ53
