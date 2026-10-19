import KrebsSankarQ53.PairSquareIdentity

/-!
# The centralizer of a noncommuting pair

The centralizer has exponent two and is exactly the center. Every
element of the ambient group has square either one or the common
nontrivial square of the chosen pair. These statements hold without
any finiteness hypothesis.
-/

namespace KrebsSankarQ53

theorem no_d8_section_pair_centralizer_square_one
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) (i j h : G)
    (hne : i * j ≠ j * i)
    (hi : h * i = i * h) (hj : h * j = j * h) : h ^ 2 = 1 := by
  have hne' : (i * h) * j ≠ j * (i * h) := by
    intro heq
    apply hne
    apply mul_right_cancel (b := h)
    calc
      (i * j) * h = i * (h * j) := by rw [hj]; group
      _ = (i * h) * j := by group
      _ = j * (i * h) := heq
      _ = (j * i) * h := by group
  have hpair := no_d8_section_noncommuting_pair_square_identity hG hno i j hne
  have hprod := no_d8_section_noncommuting_pair_square_identity hG hno (i * h) j hne'
  have hpow : (i * h) ^ 2 = i ^ 2 * h ^ 2 :=
    (show Commute i h from hi.symm).mul_pow 2
  apply mul_left_cancel (a := i ^ 2)
  calc
    i ^ 2 * h ^ 2 = (i * h) ^ 2 := hpow.symm
    _ = j ^ 2 := hprod.1
    _ = i ^ 2 * 1 := by rw [← hpair.1, mul_one]

theorem no_d8_section_pair_centralizer_iff_involution
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) (i j h : G)
    (hne : i * j ≠ j * i) :
    (h * i = i * h ∧ h * j = j * h) ↔ h * h = 1 := by
  constructor
  · rintro ⟨hi, hj⟩
    simpa only [pow_two] using
      no_d8_section_pair_centralizer_square_one hG hno i j h hne hi hj
  · intro hh
    exact ⟨(no_d8_section_involutions_central hG hno i h hh).symm,
      (no_d8_section_involutions_central hG hno j h hh).symm⟩

theorem no_d8_section_pair_centralizer_is_central
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) (i j h : G)
    (hne : i * j ≠ j * i)
    (hi : h * i = i * h) (hj : h * j = j * h) :
    ∀ g : G, g * h = h * g := by
  intro g
  apply no_d8_section_involutions_central hG hno g h
  simpa only [pow_two] using
    no_d8_section_pair_centralizer_square_one hG hno i j h hne hi hj

/-- A single nontrivial square accounts for all nonidentity squares. -/
theorem no_d8_section_all_squares_one_or_pair_square
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) (i j : G)
    (hne : i * j ≠ j * i) (g : G) :
    g ^ 2 = 1 ∨ g ^ 2 = i ^ 2 := by
  by_cases hi : g * i = i * g
  · by_cases hj : g * j = j * g
    · exact Or.inl
        (no_d8_section_pair_centralizer_square_one hG hno i j g hne hi hj)
    · right
      exact (no_d8_section_noncommuting_pair_square_identity hG hno g j hj).1.trans
        (no_d8_section_noncommuting_pair_square_identity hG hno i j hne).1.symm
  · exact Or.inr
      (no_d8_section_noncommuting_pair_square_identity hG hno g i hi).1

theorem no_d8_section_all_commutators_one_or_pair_square
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) (i j : G)
    (hne : i * j ≠ j * i) (g h : G) :
    commutatorTerm g h = 1 ∨ commutatorTerm g h = i ^ 2 := by
  by_cases hcomm : g * h = h * g
  · exact Or.inl ((commutatorTerm_eq_one_iff g h).2 hcomm)
  · have hpair := no_d8_section_noncommuting_pair_square_identity hG hno g h hcomm
    rcases no_d8_section_all_squares_one_or_pair_square hG hno i j hne g with hg | hg
    · exact False.elim (hpair.2.2.2 hg)
    · exact Or.inr (hpair.2.1.trans hg)

end KrebsSankarQ53
