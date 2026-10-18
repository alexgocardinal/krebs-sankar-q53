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

end KrebsSankarQ53
