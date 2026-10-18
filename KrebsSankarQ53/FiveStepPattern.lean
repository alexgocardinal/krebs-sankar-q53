import KrebsSankarQ53.CycleLift
import KrebsSankarQ53.ExponentFourCore

/-!
# A five-step walk in an exponent-four group

The walk with successive steps `a, b, c, b, c`, where
`a = ((b * c) ^ 2)⁻¹`, closes. Exponent four makes `a` an involution,
so its symmetric connection set has at most five elements. Choosing
`b` and `c` over suitable D8 elements is a separate next step.
-/

namespace KrebsSankarQ53

variable {G : Type*} [Group G]

/-- The step that closes a walk with steps `a, b, c, b, c`. -/
def fiveStepAnchor (b c : G) : G := ((b * c) ^ 2)⁻¹

theorem fiveStepAnchor_involution (hG : ExponentFour G) (b c : G) :
    fiveStepAnchor b c * fiveStepAnchor b c = 1 := by
  have hsq : (b * c) ^ 2 * (b * c) ^ 2 = 1 :=
    square_is_involution hG (b * c)
  change ((b * c) ^ 2)⁻¹ * ((b * c) ^ 2)⁻¹ = 1
  rw [involution_inv hsq]
  exact hsq

theorem fiveStep_pattern (b c : G) :
    fiveCycleSteps 1 (fiveStepAnchor b c)
      (fiveStepAnchor b c * b)
      (fiveStepAnchor b c * b * c)
      (fiveStepAnchor b c * b * c * b) =
      [fiveStepAnchor b c, b, c, b, c] := by
  let a := fiveStepAnchor b c
  have hclose : a * b * c * b * c = 1 := by
    dsimp [a, fiveStepAnchor]
    calc
      ((b * c) ^ 2)⁻¹ * b * c * b * c =
          ((b * c) ^ 2)⁻¹ * ((b * c) * (b * c)) := by
            simp only [mul_assoc]
      _ = ((b * c) ^ 2)⁻¹ * (b * c) ^ 2 := by rw [pow_two]
      _ = 1 := inv_mul_cancel _
  have h₀ : (1 : G)⁻¹ * a = a := by simp
  have h₁ : a⁻¹ * (a * b) = b := by group
  have h₂ : (a * b)⁻¹ * (a * b * c) = c := by group
  have h₃ : (a * b * c)⁻¹ * (a * b * c * b) = b := by group
  have h₄ : (a * b * c * b)⁻¹ * (1 : G) = c := by
    calc
      (a * b * c * b)⁻¹ * (1 : G) =
          (a * b * c * b)⁻¹ * ((a * b * c * b) * c) := by rw [hclose]
      _ = c := by group
  change fiveCycleSteps 1 a (a * b) (a * b * c) (a * b * c * b) =
    [a, b, c, b, c]
  simp only [fiveCycleSteps, h₀, h₁, h₂, h₃, h₄]

/-- The resulting symmetric connection set is finite and has at most five
elements. This statement does not yet assert three-colorability. -/
theorem fiveStepConnection_finite_card_le_five
    (hG : ExponentFour G) (b c : G) :
    (fiveCycleConnection 1 (fiveStepAnchor b c)
      (fiveStepAnchor b c * b)
      (fiveStepAnchor b c * b * c)
      (fiveStepAnchor b c * b * c * b)).Finite ∧
    (fiveCycleConnection 1 (fiveStepAnchor b c)
      (fiveStepAnchor b c * b)
      (fiveStepAnchor b c * b * c)
      (fiveStepAnchor b c * b * c * b)).ncard ≤ 5 := by
  exact fiveCycleConnection_finite_card_le_five_of_step_pattern
    1 (fiveStepAnchor b c) (fiveStepAnchor b c * b)
    (fiveStepAnchor b c * b * c) (fiveStepAnchor b c * b * c * b)
    (fiveStepAnchor b c) b c
    (fiveStepAnchor_involution hG b c) (fiveStep_pattern b c)

/-- The five-step construction lifts a three-coloring while its odd closed
walk rules out two colors. The image-membership hypotheses will be supplied
by the explicit D8 quotient in the next theorem. -/
theorem fiveStep_lift {D : Type*} [Group D]
    (hG : ExponentFour G) (f : G →* D)
    (T : Set D) (color : D → Fin 3)
    (hcolor : CayleyProperColoring T color)
    (hT : ∀ t ∈ T, t⁻¹ ∈ T)
    (b c : G) (ha : f (fiveStepAnchor b c) ∈ T)
    (hb : f b ∈ T) (hc : f c ∈ T) :
    ∃ S : Set G, S.Finite ∧ S.ncard ≤ 5 ∧
      (∃ d : G → Fin 3, CayleyProperColoring S d) ∧
      ¬ ∃ d : G → Fin 2, CayleyProperColoring S d := by
  let a := fiveStepAnchor b c
  let v₀ : G := 1
  let v₁ : G := a
  let v₂ : G := a * b
  let v₃ : G := a * b * c
  let v₄ : G := a * b * c * b
  have hsteps : ∀ s ∈ fiveCycleSteps v₀ v₁ v₂ v₃ v₄, f s ∈ T := by
    intro s hs
    change s ∈ fiveCycleSteps 1 (fiveStepAnchor b c)
      (fiveStepAnchor b c * b) (fiveStepAnchor b c * b * c)
      (fiveStepAnchor b c * b * c * b) at hs
    rw [fiveStep_pattern b c] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hb
    · exact hc
  rcases fiveStepConnection_finite_card_le_five hG b c with ⟨hfinite, hcard⟩
  rcases fiveCycle_lift f T color hcolor hT v₀ v₁ v₂ v₃ v₄ hsteps with
    ⟨hproper, hnotwo⟩
  exact ⟨fiveCycleConnection v₀ v₁ v₂ v₃ v₄,
    hfinite, hcard, ⟨fun x => color (f x), hproper⟩, hnotwo⟩

end KrebsSankarQ53
