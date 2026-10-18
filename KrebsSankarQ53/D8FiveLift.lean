import KrebsSankarQ53.FiveStepPattern
import KrebsSankarQ53.SubgroupLift

/-!
# The five-generator bound for a dihedral section

We choose lifts of `s` and `rs` (labels 4 and 5). Their product maps to
`r⁻¹`, so the anchor `((b*c)^2)⁻¹` maps to `r²` (label 2). The five-step
construction then gives the sharper bound in the paper.
-/

namespace KrebsSankarQ53

/-- The three steps chosen in D8 belong to its three-element connection set. -/
theorem d8_fiveStep_membership :
    fiveStepAnchor (⟨4⟩ : D8) ⟨5⟩ ∈ d8Connection ∧
      (⟨4⟩ : D8) ∈ d8Connection ∧ (⟨5⟩ : D8) ∈ d8Connection := by
  have hsquare : ((⟨4⟩ : D8) * ⟨5⟩) ^ 2 = ⟨2⟩ := by
    apply D8.ext
    simp only [pow_two]
    change dmul (dmul 4 5) (dmul 4 5) = 2
    decide
  have hinvol : (⟨2⟩ : D8) * ⟨2⟩ = 1 := by
    apply D8.ext
    change dmul 2 2 = 0
    decide
  have hanchor : fiveStepAnchor (⟨4⟩ : D8) ⟨5⟩ = ⟨2⟩ := by
    unfold fiveStepAnchor
    rw [hsquare]
    exact involution_inv hinvol
  constructor
  · change (fiveStepAnchor (⟨4⟩ : D8) ⟨5⟩).val ∈ generators
    rw [hanchor]
    decide
  constructor
  · change (⟨4⟩ : D8).val ∈ generators
    decide
  · change (⟨5⟩ : D8).val ∈ generators
    decide

/-- An exponent-four group surjecting onto D8 has a three-chromatic Cayley
graph with at most five generators. -/
theorem d8_quotient_has_three_chromatic_cayley_five
    {H : Type*} [Group H] (hH : ExponentFour H)
    (f : H →* D8) (hf : Function.Surjective f) :
    ∃ S : Set H, S.Finite ∧ S.ncard ≤ 5 ∧
      (∃ c : H → Fin 3, CayleyProperColoring S c) ∧
      ¬ ∃ c : H → Fin 2, CayleyProperColoring S c := by
  let b : H := Classical.choose (hf ⟨4⟩)
  let c : H := Classical.choose (hf ⟨5⟩)
  have hb : f b = (⟨4⟩ : D8) := Classical.choose_spec (hf ⟨4⟩)
  have hc : f c = (⟨5⟩ : D8) := Classical.choose_spec (hf ⟨5⟩)
  rcases d8_fiveStep_membership with ⟨haD, hbD, hcD⟩
  have hmap : f (fiveStepAnchor b c) =
      fiveStepAnchor (f b) (f c) := by
    simp [fiveStepAnchor]
  have ha : f (fiveStepAnchor b c) ∈ d8Connection := by
    rw [hmap, hb, hc]
    exact haD
  have hbmem : f b ∈ d8Connection := by rw [hb]; exact hbD
  have hcmem : f c ∈ d8Connection := by rw [hc]; exact hcD
  exact fiveStep_lift hH f d8Connection
    (fun v => threeColor v.val) d8_threeColor_proper
    (fun _ ht => d8Connection_inv_mem ht) b c ha hbmem hcmem

/-- The exponent-four property passes to a subgroup. -/
theorem exponentFour_subgroup {G : Type*} [Group G]
    (hG : ExponentFour G) (H : Subgroup G) : ExponentFour H := by
  intro x
  apply Subtype.ext
  change (x : G) ^ 4 = 1
  exact hG x

/-- The paper's positive direction, including its five-generator bound:
a D8 section of an exponent-four group supplies an exact three-chromatic
Cayley graph in the whole group. -/
theorem d8_section_has_three_chromatic_cayley_five
    {G : Type*} [Group G] (hG : ExponentFour G)
    (H : Subgroup G) (f : H →* D8) (hf : Function.Surjective f) :
    ∃ S : Set G, S.Finite ∧ S.ncard ≤ 5 ∧
      (∃ c : G → Fin 3, CayleyProperColoring S c) ∧
      ¬ ∃ c : G → Fin 2, CayleyProperColoring S c := by
  rcases d8_quotient_has_three_chromatic_cayley_five
      (exponentFour_subgroup hG H) f hf with
    ⟨S, hfinite, hcard, ⟨c, hc⟩, hn⟩
  have hfiniteG : (subgroupConnection H S).Finite := by
    rw [subgroupConnection_eq_image]
    exact hfinite.image Subtype.val
  have hcardG : (subgroupConnection H S).ncard ≤ 5 := by
    rw [subgroupConnection_ncard]
    exact hcard
  exact ⟨subgroupConnection H S,
    hfiniteG, hcardG,
    subgroup_color_extend H S 3 c hc, subgroup_no_two_extend H S hn⟩

end KrebsSankarQ53
