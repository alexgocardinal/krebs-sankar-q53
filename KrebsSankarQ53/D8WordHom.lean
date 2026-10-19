import KrebsSankarQ53.D8WordActions

/-!
# The D8 word homomorphism

Right multiplication by the concrete rotation and reflection has already
been verified. Every concrete D8 element is a product of a rotation power
and at most one reflection, so word evaluation preserves all products.
-/

namespace KrebsSankarQ53

theorem d8Word_one {G : Type*} [Group G] (a b : G) :
    d8Word a b (1 : D8) = 1 := by
  change d8Word a b ⟨0⟩ = 1
  simp [d8Word]

/-- Evaluation of the eight normal forms preserves multiplication. -/
theorem d8Word_mul {G : Type*} [Group G]
    (hG : ExponentFour G) {a b : G}
    (ha : a * a = 1) (hb : b * b = 1) (x y : D8) :
    d8Word a b (x * y) = d8Word a b x * d8Word a b y := by
  let r : D8 := d8First * d8Second
  have hpow : ∀ n : ℕ, ∀ z : D8,
      d8Word a b (z * r ^ n) = d8Word a b z * (a * b) ^ n := by
    intro n
    induction n with
    | zero =>
        intro z
        simp
    | succ n ih =>
        intro z
        calc
          d8Word a b (z * r ^ (n + 1)) =
              d8Word a b ((z * r ^ n) * r) := by rw [pow_succ, mul_assoc]
          _ = d8Word a b (z * r ^ n) * (a * b) :=
            d8Word_mul_rotation hG ha hb _
          _ = (d8Word a b z * (a * b) ^ n) * (a * b) := by rw [ih z]
          _ = d8Word a b z * (a * b) ^ (n + 1) := by rw [pow_succ, mul_assoc]
  have hrotation (n : ℕ) : d8Word a b (r ^ n) = (a * b) ^ n := by
    have h := hpow n (1 : D8)
    simpa only [one_mul, d8Word_one, one_mul] using h
  obtain ⟨i, hy | hy⟩ := d8_normal_forms y
  · rw [hy]
    exact (hpow i.val x).trans (by rw [hrotation])
  · rw [hy]
    calc
      d8Word a b (x * (r ^ i.val * d8First)) =
          d8Word a b ((x * r ^ i.val) * d8First) := by rw [mul_assoc]
      _ = d8Word a b (x * r ^ i.val) * a := d8Word_mul_first ha _
      _ = (d8Word a b x * (a * b) ^ i.val) * a := by rw [hpow i.val x]
      _ = d8Word a b x * d8Word a b (r ^ i.val * d8First) := by
        rw [d8Word_mul_first ha, hrotation, mul_assoc]

/-- The word map as a group homomorphism into the generated subgroup. -/
def d8WordHom {G : Type*} [Group G] (hG : ExponentFour G)
    {a b : G} (ha : a * a = 1) (hb : b * b = 1) :
    D8 →* Subgroup.closure ({a, b} : Set G) where
  toFun := d8WordInClosure a b
  map_one' := by
    apply Subtype.ext
    change d8Word a b (1 : D8) = 1
    exact d8Word_one a b
  map_mul' x y := by
    apply Subtype.ext
    change d8Word a b (x * y) = d8Word a b x * d8Word a b y
    exact d8Word_mul hG ha hb x y

end KrebsSankarQ53
