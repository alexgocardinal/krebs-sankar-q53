import KrebsSankarQ53.D8WordMap

/-!
# Multiplying rotation and reflection words

The reflection conjugates the rotation to its inverse. The same identity
holds for every integer power and controls products of reflected rotations.
-/

namespace KrebsSankarQ53

/-- Moving the first involution past an arbitrary rotation power reverses
that power. -/
theorem involution_mul_rotation_zpow
    {G : Type*} [Group G] {a b : G}
    (ha : a * a = 1) (hb : b * b = 1) (k : ℤ) :
    a * (a * b) ^ k = ((a * b) ^ k)⁻¹ * a := by
  let r := a * b
  have hbase : a * r * a⁻¹ = r⁻¹ := by
    simpa only [r, involution_inv ha] using
      involution_reflects_product ha hb
  have hpower : a * r ^ k * a⁻¹ = (r ^ k)⁻¹ := by
    calc
      a * r ^ k * a⁻¹ = (a * r * a⁻¹) ^ k := (conj_zpow).symm
      _ = (r⁻¹) ^ k := by rw [hbase]
      _ = (r ^ k)⁻¹ := by simp
  change a * r ^ k = (r ^ k)⁻¹ * a
  calc
    a * r ^ k = (a * r ^ k * a⁻¹) * a := by group
    _ = (r ^ k)⁻¹ * a := by rw [hpower]

/-- A reflected rotation multiplied by a rotation has the reversed
rotation power on its right. -/
theorem reflected_rotation_mul_rotation_zpow
    {G : Type*} [Group G] {a b : G}
    (ha : a * a = 1) (hb : b * b = 1) (i j : ℤ) :
    ((a * b) ^ i * a) * (a * b) ^ j =
      (a * b) ^ i * ((a * b) ^ j)⁻¹ * a := by
  rw [mul_assoc, involution_mul_rotation_zpow ha hb j]
  group

/-- The product of two reflected rotations is a rotation. -/
theorem reflected_rotation_mul_reflected_rotation_zpow
    {G : Type*} [Group G] {a b : G}
    (ha : a * a = 1) (hb : b * b = 1) (i j : ℤ) :
    ((a * b) ^ i * a) * ((a * b) ^ j * a) =
      (a * b) ^ i * ((a * b) ^ j)⁻¹ := by
  calc
    ((a * b) ^ i * a) * ((a * b) ^ j * a) =
        (((a * b) ^ i * a) * (a * b) ^ j) * a := by group
    _ = ((a * b) ^ i * ((a * b) ^ j)⁻¹ * a) * a := by
      rw [reflected_rotation_mul_rotation_zpow ha hb i j]
    _ = (a * b) ^ i * ((a * b) ^ j)⁻¹ := by
      rw [mul_assoc, ha]
      simp

end KrebsSankarQ53
