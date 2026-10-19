import KrebsSankarQ53.QuaternionPair

/-!
# Covering the group by its quaternion subgroup and its center

For a fixed noncommuting pair `i,j`, multiplying any group element
by one of `1,i,j,i*j` cancels both commutators. The corrected element
has square one and is central. Thus `G = <i,j> Z(G)` even when `G`
is infinite. Splitting the common central involution off the center
is the remaining complement step.
-/

namespace KrebsSankarQ53

theorem commutatorTerm_mul_left_of_central
    {G : Type*} [Group G] (a b t : G)
    (hc : a * commutatorTerm b t = commutatorTerm b t * a) :
    commutatorTerm (a * b) t = commutatorTerm b t * commutatorTerm a t := by
  calc
    commutatorTerm (a * b) t =
        a * commutatorTerm b t * a⁻¹ * commutatorTerm a t := by
      dsimp [commutatorTerm]
      group
    _ = commutatorTerm b t * commutatorTerm a t := by rw [hc]; group

theorem no_d8_section_pair_correction
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) (i j : G) (hne : i * j ≠ j * i) (g : G) :
    ∃ k ∈ Subgroup.closure ({i, j} : Set G),
      commutatorTerm (k * g) i = 1 ∧ commutatorTerm (k * g) j = 1 := by
  let H : Subgroup G := Subgroup.closure ({i, j} : Set G)
  have hiH : i ∈ H := Subgroup.subset_closure (by simp)
  have hjH : j ∈ H := Subgroup.subset_closure (by simp)
  have hformula (a b t : G) :
      commutatorTerm (a * b) t = commutatorTerm b t * commutatorTerm a t :=
    commutatorTerm_mul_left_of_central a b t
      (no_d8_section_commutators_central hG hno b t a).symm
  have hij : commutatorTerm i j = i ^ 2 :=
    no_d8_section_noncommuting_commutator_eq_square hG hno i j hne
  have hji : commutatorTerm j i = i ^ 2 := by
    rw [commutatorTerm_reverse, hij, involution_inv (square_is_involution hG i)]
  have hii : commutatorTerm i i = 1 := (commutatorTerm_eq_one_iff i i).2 rfl
  have hjj : commutatorTerm j j = 1 := (commutatorTerm_eq_one_iff j j).2 rfl
  rcases no_d8_section_commutator_mem_squarePair hG hno i g with hi | hi <;>
    rcases no_d8_section_commutator_mem_squarePair hG hno j g with hj | hj
  · refine ⟨1, H.one_mem, ?_, ?_⟩
    · rw [one_mul, commutatorTerm_reverse g i, hi, inv_one]
    · rw [one_mul, commutatorTerm_reverse g j, hj, inv_one]
  · refine ⟨i, hiH, ?_, ?_⟩
    · rw [hformula, commutatorTerm_reverse g i, hi, inv_one, hii, one_mul]
    · rw [hformula, commutatorTerm_reverse g j, hj, hij,
        ← (no_d8_section_noncommuting_pair_square_identity hG hno i j hne).1,
        involution_inv (square_is_involution hG i), square_is_involution hG i]
  · refine ⟨j, hjH, ?_, ?_⟩
    · rw [hformula, commutatorTerm_reverse g i, hi, hji,
        involution_inv (square_is_involution hG i), square_is_involution hG i]
    · rw [hformula, commutatorTerm_reverse g j, hj, inv_one, hjj, one_mul]
  · refine ⟨i * j, H.mul_mem hiH hjH, ?_, ?_⟩
    · rw [hformula, hformula i j i, commutatorTerm_reverse g i, hi, hji, hii,
        mul_one, involution_inv (square_is_involution hG i), square_is_involution hG i]
    · rw [hformula, hformula i j j, commutatorTerm_reverse g j, hj, hjj, hij,
        one_mul, ← (no_d8_section_noncommuting_pair_square_identity hG hno i j hne).1,
        involution_inv (square_is_involution hG i), square_is_involution hG i]

/-- Every element is a quaternion word times a central involution. -/
theorem no_d8_section_quaternion_center_cover
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) (i j : G) (hne : i * j ≠ j * i) (g : G) :
    ∃ k ∈ Subgroup.closure ({i, j} : Set G),
      ∃ t : G, t * t = 1 ∧ (∀ a : G, a * t = t * a) ∧ g = k * t := by
  obtain ⟨k, hk, hi, hj⟩ := no_d8_section_pair_correction hG hno i j hne g
  have hki : (k * g) * i = i * (k * g) := (commutatorTerm_eq_one_iff _ _).1 hi
  have hkj : (k * g) * j = j * (k * g) := (commutatorTerm_eq_one_iff _ _).1 hj
  refine ⟨k⁻¹, (Subgroup.closure ({i, j} : Set G)).inv_mem hk, k * g, ?_, ?_, ?_⟩
  · exact (no_d8_section_pair_centralizer_iff_involution hG hno i j (k * g) hne).1 ⟨hki, hkj⟩
  · exact no_d8_section_pair_centralizer_is_central hG hno i j (k * g) hne hki hkj
  · group

end KrebsSankarQ53
