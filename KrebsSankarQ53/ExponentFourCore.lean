import KrebsSankarQ53.CayleyCore

/-!
# First structural facts for the reverse implication

This module isolates elementary consequences of exponent dividing four.
It does not yet prove the no-D8 classification.
-/

namespace KrebsSankarQ53

/-- Every element of the group has fourth power equal to one. -/
def ExponentFour (G : Type*) [Group G] : Prop :=
  ∀ x : G, x ^ 4 = 1

/-- In a group of exponent dividing four, every square is an involution. -/
theorem square_is_involution {G : Type*} [Group G]
    (hG : ExponentFour G) (x : G) : x ^ 2 * x ^ 2 = 1 := by
  calc
    x ^ 2 * x ^ 2 = x ^ (2 + 2) := (pow_add x 2 2).symm
    _ = x ^ 4 := by rfl
    _ = 1 := hG x

/-- An element whose square is one is its own inverse. -/
theorem involution_inv {G : Type*} [Group G] {x : G}
    (hx : x * x = 1) : x⁻¹ = x := by
  calc
    x⁻¹ = x⁻¹ * (x * x) := by rw [hx]; simp
    _ = (x⁻¹ * x) * x := by rw [mul_assoc]
    _ = x := by simp

/-- Noncommuting involutions multiply to an element of order four. -/
theorem noncommuting_involutions_product_order_four
    {G : Type*} [Group G] (hG : ExponentFour G)
    {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hne : a * b ≠ b * a) :
    (a * b) ^ 4 = 1 ∧ (a * b) ^ 2 ≠ 1 := by
  refine ⟨hG (a * b), ?_⟩
  intro hab
  have hcomm : a * b = b * a := by
    calc
      a * b = (a * b)⁻¹ := (involution_inv (by simpa only [pow_two] using hab)).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [involution_inv hb, involution_inv ha]
  exact hne hcomm

end KrebsSankarQ53
