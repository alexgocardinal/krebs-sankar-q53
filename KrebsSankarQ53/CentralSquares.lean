import KrebsSankarQ53.InvolutionsCentral

/-!
# Central squares and the central involution subgroup

These consequences use the verified fact that every square-one
element is central when an exponent-four group has no D8 section.
-/

namespace KrebsSankarQ53

theorem no_d8_section_squares_central
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) (x y : G) :
    x ^ 2 * y = y * x ^ 2 :=
  (no_d8_section_involutions_central hG hno y (x ^ 2)
    (square_is_involution hG x)).symm

theorem no_d8_section_squares_in_involutionSubgroup
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) (x : G) :
    x ^ 2 ∈ involutionSubgroup
      (no_d8_section_involutions_commute hG hno) := by
  change x ^ 2 * x ^ 2 = 1
  exact square_is_involution hG x

theorem no_d8_section_involutionSubgroup_central
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) (g : G)
    (z : involutionSubgroup
      (no_d8_section_involutions_commute hG hno)) :
    g * (z : G) = (z : G) * g := by
  apply no_d8_section_involutions_central hG hno g z
  exact z.property

end KrebsSankarQ53
