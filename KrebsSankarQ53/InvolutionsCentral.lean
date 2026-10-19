import KrebsSankarQ53.SectionTransfer

/-!
# Involutions are central without a D8 section

If a conjugator moves an involution, the quotient of their generated
subgroup by its central square contains two noncommuting involutions.
The resulting D8 section lifts through the quotient and subgroup,
contradicting the hypothesis.
-/

namespace KrebsSankarQ53

theorem no_d8_section_involutions_central
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) (x t : G)
    (ht : t * t = 1) : x * t = t * x := by
  by_contra hne
  let H : Subgroup G := Subgroup.closure ({x, t} : Set G)
  let W : Subgroup H :=
    (squarePairSubgroup (x ^ 2) (square_is_involution hG x)).subgroupOf H
  letI : W.Normal := local_square_pair_normal hG hno x t ht
  obtain ⟨a, b, ha, hb, hab⟩ :=
    local_square_quotient_noncommuting_involutions hG hno ht hne W rfl
  have hH : ExponentFour H := by
    intro y
    apply Subtype.ext
    exact hG y
  have hQ : ExponentFour (H ⧸ W) := exponentFour_quotient hH W
  have hsection : HasD8Section (H ⧸ W) :=
    noncommuting_involutions_have_d8_section hQ ha hb hab
  exact hno (hasD8Section_of_subgroup H
    (hasD8Section_of_quotient W hsection))

end KrebsSankarQ53
