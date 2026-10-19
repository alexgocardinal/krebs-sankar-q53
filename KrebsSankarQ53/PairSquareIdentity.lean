import KrebsSankarQ53.PairRelations

/-!
# The noncommuting-pair square identity

Quotient by the central subgroup `{1, x²}`. The image of `x` is an
involution, hence central in the quotient if there is no D8 section.
The original commutator therefore belongs to `{1, x²}`. For a
noncommuting pair it is nontrivial, so it equals `x²`. Interchanging
the pair gives `y²` as well. No finiteness or choice of a linear
functional is needed.
-/

namespace KrebsSankarQ53

theorem no_d8_section_squarePairSubgroup_normal
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) (x : G) :
    (squarePairSubgroup (x ^ 2) (square_is_involution hG x)).Normal := by
  refine ⟨?_⟩
  intro n hn g
  change n = 1 ∨ n = x ^ 2 at hn
  change g * n * g⁻¹ = 1 ∨ g * n * g⁻¹ = x ^ 2
  rcases hn with rfl | rfl
  · left; group
  · right
    calc
      g * x ^ 2 * g⁻¹ = (x ^ 2 * g) * g⁻¹ := by
        rw [no_d8_section_squares_central hG hno x g]
      _ = x ^ 2 := by group

theorem no_d8_section_commutator_mem_squarePair
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) (x y : G) :
    commutatorTerm x y = 1 ∨ commutatorTerm x y = x ^ 2 := by
  let N : Subgroup G := squarePairSubgroup (x ^ 2) (square_is_involution hG x)
  letI : N.Normal := no_d8_section_squarePairSubgroup_normal hG hno x
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hQ : ExponentFour (G ⧸ N) := exponentFour_quotient hG N
  have hnoQ : ¬ HasD8Section (G ⧸ N) :=
    fun h => hno (hasD8Section_of_quotient N h)
  have hxN : x * x ∈ N := by
    change x * x = 1 ∨ x * x = x ^ 2
    exact Or.inr (pow_two x).symm
  have hqx : q x * q x = 1 := by
    rw [← map_mul]
    simpa only [q, QuotientGroup.mk'_apply] using
      (QuotientGroup.eq_one_iff (x * x)).2 hxN
  have hcomm : q x * q y = q y * q x :=
    (no_d8_section_involutions_central hQ hnoQ (q y) (q x) hqx).symm
  have hzero : q (commutatorTerm x y) = 1 := by
    have hc := (commutatorTerm_eq_one_iff (q x) (q y)).2 hcomm
    simpa [commutatorTerm, map_mul] using hc
  have hmem : commutatorTerm x y ∈ N := by
    apply (QuotientGroup.eq_one_iff (commutatorTerm x y)).1
    simpa only [q, QuotientGroup.mk'_apply] using hzero
  exact hmem

theorem no_d8_section_noncommuting_commutator_eq_square
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) (x y : G)
    (hne : x * y ≠ y * x) : commutatorTerm x y = x ^ 2 := by
  rcases no_d8_section_commutator_mem_squarePair hG hno x y with h | h
  · exact False.elim (hne ((commutatorTerm_eq_one_iff x y).1 h))
  · exact h

theorem commutatorTerm_reverse
    {G : Type*} [Group G] (x y : G) :
    commutatorTerm y x = (commutatorTerm x y)⁻¹ := by
  dsimp [commutatorTerm]
  group

/-- The key pair identity, valid also for infinite groups. -/
theorem no_d8_section_noncommuting_pair_square_identity
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) (x y : G)
    (hne : x * y ≠ y * x) :
    x ^ 2 = y ^ 2 ∧ commutatorTerm x y = x ^ 2 ∧
      (x * y) ^ 2 = x ^ 2 ∧ x ^ 2 ≠ 1 := by
  have hx := no_d8_section_noncommuting_commutator_eq_square hG hno x y hne
  have hy := no_d8_section_noncommuting_commutator_eq_square hG hno y x
    (Ne.symm hne)
  have hrev : commutatorTerm y x = commutatorTerm x y := by
    rw [commutatorTerm_reverse, involution_inv
      (no_d8_section_commutator_involution hG hno x y)]
  have hsq : x ^ 2 = y ^ 2 := hx.symm.trans (hrev.symm.trans hy)
  refine ⟨hsq, hx, ?_,
    (no_d8_section_noncommuting_pair_core hG hno x y hne).1⟩
  rw [no_d8_section_pair_product_square hG hno x y, hx, ← hsq,
    square_is_involution hG x, mul_one]

end KrebsSankarQ53
