import KrebsSankarQ53.Classification

/-!
# Exact three-chromatic Cayley graphs with at most five connection elements

The existing five-step construction already yields a symmetric set of
cardinality at most five. These statements retain inverse-closure in the
exported interface, so no second symmetrization is needed.
-/

namespace KrebsSankarQ53

universe u

/-- The explicit five-step connection is inverse-closed, identity-free,
three-chromatic, and has cardinality at most five. -/
theorem d8_quotient_exact_three_card_le_five
    {H : Type*} [Group H] (hH : ExponentFour H)
    (f : H →* D8) (hf : Function.Surjective f) :
    ∃ S : Set H, S.Finite ∧ S.ncard ≤ 5 ∧ IsExactThreeCayleyConnection S := by
  classical
  let b : H := Classical.choose (hf ⟨4⟩)
  let c : H := Classical.choose (hf ⟨5⟩)
  have hb : f b = (⟨4⟩ : D8) := Classical.choose_spec (hf ⟨4⟩)
  have hc : f c = (⟨5⟩ : D8) := Classical.choose_spec (hf ⟨5⟩)
  let a : H := fiveStepAnchor b c
  let S : Set H := fiveCycleConnection 1 a (a * b) (a * b * c) (a * b * c * b)
  rcases d8_fiveStep_membership with ⟨haD, hbD, hcD⟩
  have hanchor : f a = fiveStepAnchor (f b) (f c) := by
    simp [a, fiveStepAnchor]
  have ha : f a ∈ d8Connection := by
    rw [hanchor, hb, hc]
    exact haD
  have hbmem : f b ∈ d8Connection := by
    rw [hb]
    exact hbD
  have hcmem : f c ∈ d8Connection := by
    rw [hc]
    exact hcD
  have hsteps : ∀ s ∈ fiveCycleSteps 1 a (a * b) (a * b * c) (a * b * c * b),
      f s ∈ d8Connection := by
    intro s hs
    change s ∈ fiveCycleSteps 1 (fiveStepAnchor b c)
      (fiveStepAnchor b c * b) (fiveStepAnchor b c * b * c)
      (fiveStepAnchor b c * b * c * b) at hs
    rw [fiveStep_pattern b c] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact ha
    · exact hbmem
    · exact hcmem
    · exact hbmem
    · exact hcmem
  rcases fiveCycle_lift f d8Connection (fun v => threeColor v.val)
      d8_threeColor_proper (fun _ ht => d8Connection_inv_mem ht)
      1 a (a * b) (a * b * c) (a * b * c * b) hsteps with ⟨hproper, hn⟩
  rcases fiveStepConnection_finite_card_le_five hH b c with ⟨hfinite, hcard⟩
  refine ⟨S, hfinite, hcard, ?_, ?_, ⟨fun x => threeColor (f x).val, hproper⟩, hn⟩
  · intro s hs
    exact fiveCycleConnection_inv_mem 1 a (a * b) (a * b * c) (a * b * c * b) hs
  · intro h1
    exact hproper 1 1 ⟨1, h1, by simp⟩ rfl

/-- A dihedral section gives an exact three-chromatic Cayley graph on the
ambient exponent-four group with at most five connection elements. -/
theorem d8_section_exact_three_card_le_five
    {G : Type*} [Group G] (hG : ExponentFour G) (hD : HasD8Section G) :
    ∃ S : Set G, S.Finite ∧ S.ncard ≤ 5 ∧ IsExactThreeCayleyConnection S := by
  rcases hD with ⟨H, f, hf⟩
  obtain ⟨S, hfinite, hcard, hsymm, _, ⟨c, hc⟩, hn⟩ :=
    d8_quotient_exact_three_card_le_five (exponentFour_subgroup hG H) f hf
  let T : Set G := subgroupConnection H S
  have hfiniteG : T.Finite := by
    change (subgroupConnection H S).Finite
    rw [subgroupConnection_eq_image]
    exact hfinite.image Subtype.val
  have hcardG : T.ncard ≤ 5 := by
    change (subgroupConnection H S).ncard ≤ 5
    rw [subgroupConnection_ncard]
    exact hcard
  obtain ⟨C, hC⟩ := subgroup_color_extend H S 3 c hc
  refine ⟨T, hfiniteG, hcardG, ?_, ?_, ⟨C, hC⟩, subgroup_no_two_extend H S hn⟩
  · intro s hs
    rcases hs with ⟨t, ht, rfl⟩
    exact ⟨t⁻¹, hsymm t ht, rfl⟩
  · intro h1
    exact hC 1 1 ⟨1, h1, by simp⟩ rfl

/-- The full classification, with the sharpened five-element bound.
The hypotheses are only exponent dividing four and noncommutativity. -/
theorem q53_full_classification_five
    {G : Type u} [Group G] (hG : ExponentFour G)
    (hnonabelian : ∃ i j : G, i * j ≠ j * i) :
    (HasExactThreeCayley G ↔ HasD8Section G) ∧
      (HasD8Section G ↔ ¬ IsQuaternionElementaryProduct G) ∧
        (HasD8Section G → ∃ S : Set G,
          S.Finite ∧ S.ncard ≤ 5 ∧ IsExactThreeCayleyConnection S) := by
  exact ⟨(q53_full_classification hG hnonabelian).1,
    (q53_full_classification hG hnonabelian).2.1,
    d8_section_exact_three_card_le_five hG⟩

end KrebsSankarQ53
