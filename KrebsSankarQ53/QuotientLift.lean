import KrebsSankarQ53.D8Group

/-!
# A dihedral quotient gives a three-chromatic Cayley graph

This is the quotient step of section lifting. The ambient subgroup step and
the at-most-ten bound are separate lemmas still to be formalized.
-/

namespace KrebsSankarQ53

private theorem difference_mem_of_adj {D : Type*} [Group D]
    (T : Set D) {x y : D} (h : rightCayleyAdj T x y) :
    x⁻¹ * y ∈ T := by
  rcases h with ⟨s, hs, rfl⟩
  simpa using hs

/-- A surjection to the explicit dihedral group yields an exact three-color
Cayley witness in the source group. -/
theorem d8_quotient_has_three_chromatic_cayley
    {H : Type*} [Group H] (f : H →* D8) (hf : Function.Surjective f) :
    ∃ S : Set H, (∃ c : H → Fin 3, CayleyProperColoring S c) ∧
      ¬ ∃ c : H → Fin 2, CayleyProperColoring S c := by
  let v₀ : H := Classical.choose (hf ⟨0⟩)
  let v₁ : H := Classical.choose (hf ⟨2⟩)
  let v₂ : H := Classical.choose (hf ⟨6⟩)
  let v₃ : H := Classical.choose (hf ⟨1⟩)
  let v₄ : H := Classical.choose (hf ⟨5⟩)
  have hv₀ : f v₀ = (⟨0⟩ : D8) := Classical.choose_spec (hf ⟨0⟩)
  have hv₁ : f v₁ = (⟨2⟩ : D8) := Classical.choose_spec (hf ⟨2⟩)
  have hv₂ : f v₂ = (⟨6⟩ : D8) := Classical.choose_spec (hf ⟨6⟩)
  have hv₃ : f v₃ = (⟨1⟩ : D8) := Classical.choose_spec (hf ⟨1⟩)
  have hv₄ : f v₄ = (⟨5⟩ : D8) := Classical.choose_spec (hf ⟨5⟩)
  rcases d8_fiveCycle_edges with ⟨he₀, he₁, he₂, he₃, he₄⟩
  have h₀ : f (v₀⁻¹ * v₁) ∈ d8Connection := by
    simpa [map_mul, hv₀, hv₁] using
      (difference_mem_of_adj d8Connection he₀)
  have h₁ : f (v₁⁻¹ * v₂) ∈ d8Connection := by
    simpa [map_mul, hv₁, hv₂] using
      (difference_mem_of_adj d8Connection he₁)
  have h₂ : f (v₂⁻¹ * v₃) ∈ d8Connection := by
    simpa [map_mul, hv₂, hv₃] using
      (difference_mem_of_adj d8Connection he₂)
  have h₃ : f (v₃⁻¹ * v₄) ∈ d8Connection := by
    simpa [map_mul, hv₃, hv₄] using
      (difference_mem_of_adj d8Connection he₃)
  have h₄ : f (v₄⁻¹ * v₀) ∈ d8Connection := by
    simpa [map_mul, hv₄, hv₀] using
      (difference_mem_of_adj d8Connection he₄)
  have hsteps : ∀ s ∈ fiveCycleSteps v₀ v₁ v₂ v₃ v₄,
      f s ∈ d8Connection := by
    intro s hs
    simp [fiveCycleSteps] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact h₀
    · exact h₁
    · exact h₂
    · exact h₃
    · exact h₄
  rcases fiveCycle_lift f d8Connection
      (fun v => threeColor v.val) d8_threeColor_proper
      (fun _ ht => d8Connection_inv_mem ht)
      v₀ v₁ v₂ v₃ v₄ hsteps with ⟨hcolor, hnotwo⟩
  exact ⟨fiveCycleConnection v₀ v₁ v₂ v₃ v₄,
    ⟨(fun x => threeColor (f x).val), hcolor⟩, hnotwo⟩

end KrebsSankarQ53
