import KrebsSankarQ53.RotationConjugation

/-!
# Right multiplication of evaluated D8 words

The two checks below concern right multiplication by the concrete
reflection and rotation. Their combination will establish that the word
evaluation map preserves all products.
-/

namespace KrebsSankarQ53

/-- Right multiplication by the concrete reflection evaluates as right
multiplication by the chosen involution. -/
theorem d8Word_mul_first {G : Type*} [Group G]
    {a b : G} (ha : a * a = 1) (x : D8) :
    d8Word a b (x * d8First) = d8Word a b x * a := by
  rcases x with ⟨v⟩
  change d8Word a b ⟨dmul v 4⟩ = d8Word a b ⟨v⟩ * a
  fin_cases v <;> simp [d8Word, dmul, mul_assoc, ha]

/-- Right multiplication by the concrete rotation evaluates as right
multiplication by the product of the involutions. -/
theorem d8Word_mul_rotation {G : Type*} [Group G]
    (hG : ExponentFour G) {a b : G}
    (ha : a * a = 1) (hb : b * b = 1) (x : D8) :
    d8Word a b (x * (d8First * d8Second)) =
      d8Word a b x * (a * b) := by
  have h4 : (a * b) ^ 4 = 1 := hG (a * b)
  have h3 : (a * b) ^ 3 = (a * b)⁻¹ := by
    calc
      (a * b) ^ 3 = ((a * b) ^ 3 * (a * b)) * (a * b)⁻¹ := by
        simp [mul_assoc]
      _ = (a * b) ^ 4 * (a * b)⁻¹ := by rw [← pow_succ]
      _ = (a * b)⁻¹ := by rw [h4]; simp
  have hflip : a * (a * b) = (a * b) ^ 3 * a := by
    simpa only [zpow_one, ← h3] using
      (involution_mul_rotation_zpow ha hb (1 : ℤ))
  rcases x with ⟨v⟩
  change d8Word a b ⟨dmul v (dmul 4 7)⟩ =
    d8Word a b ⟨v⟩ * (a * b)
  fin_cases v <;>
    simp [d8Word, dmul, pow_succ, mul_assoc, hflip]
  all_goals
    first
    | simpa [pow_succ, mul_assoc] using h4.symm
    | simpa [pow_succ, mul_assoc] using (hG (b * a))

end KrebsSankarQ53
