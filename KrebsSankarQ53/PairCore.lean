import KrebsSankarQ53.ClassTwo

/-!
# Noncommuting pairs in exponent-four groups without a D8 section

The squares and commutator of a noncommuting pair are central,
nonidentity involutions. This is the input for the remaining
two-generator quotient argument.
-/

namespace KrebsSankarQ53

theorem commutatorTerm_eq_one_iff
    {G : Type*} [Group G] (x y : G) :
    commutatorTerm x y = 1 ↔ x * y = y * x := by
  constructor
  · intro hc
    calc
      x * y = commutatorTerm x y * (y * x) := by
        dsimp [commutatorTerm]
        group
      _ = y * x := by rw [hc]; simp
  · intro hc
    dsimp [commutatorTerm]
    rw [hc]
    group

theorem no_d8_section_noncommuting_pair_core
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) (x y : G)
    (hne : x * y ≠ y * x) :
    x ^ 2 ≠ 1 ∧ y ^ 2 ≠ 1 ∧ commutatorTerm x y ≠ 1 ∧
      x ^ 2 * x ^ 2 = 1 ∧ y ^ 2 * y ^ 2 = 1 ∧
        commutatorTerm x y * commutatorTerm x y = 1 := by
  have hx : x ^ 2 ≠ 1 := by
    intro hx2
    have hx1 : x * x = 1 := by simpa only [pow_two] using hx2
    exact hne ((no_d8_section_involutions_central hG hno y x hx1).symm)
  have hy : y ^ 2 ≠ 1 := by
    intro hy2
    have hy1 : y * y = 1 := by simpa only [pow_two] using hy2
    exact hne (no_d8_section_involutions_central hG hno x y hy1)
  exact ⟨hx, hy, fun hc => hne ((commutatorTerm_eq_one_iff x y).mp hc),
    square_is_involution hG x, square_is_involution hG y,
    no_d8_section_commutator_involution hG hno x y⟩

theorem no_d8_section_pair_core_mem_involutions
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) (x y : G) :
    x ^ 2 ∈ involutionSubgroup
      (no_d8_section_involutions_commute hG hno) ∧
    y ^ 2 ∈ involutionSubgroup
      (no_d8_section_involutions_commute hG hno) ∧
    commutatorTerm x y ∈ involutionSubgroup
      (no_d8_section_involutions_commute hG hno) := by
  change x ^ 2 * x ^ 2 = 1 ∧ y ^ 2 * y ^ 2 = 1 ∧
    commutatorTerm x y * commutatorTerm x y = 1
  exact ⟨square_is_involution hG x, square_is_involution hG y,
    no_d8_section_commutator_involution hG hno x y⟩

end KrebsSankarQ53
