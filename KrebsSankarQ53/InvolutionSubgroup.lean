import KrebsSankarQ53.ExponentFourCore

/-!
# Commuting involutions form a subgroup

This is the next structural ingredient. A later module must derive the
commutation hypothesis from the absence of a D8 section; it is not assumed
by the final classification theorem.
-/

namespace KrebsSankarQ53

/-- Conjugation preserves the property of having square one. -/
theorem conjugate_involution {G : Type*} [Group G]
    {g x : G} (hx : x * x = 1) :
    (g * x * g⁻¹) * (g * x * g⁻¹) = 1 := by
  calc
    (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
    _ = 1 := by rw [hx]; simp

/-- If all involutions commute, they form a subgroup. -/
def involutionSubgroup {G : Type*} [Group G]
    (hcomm : ∀ a b : G, a * a = 1 → b * b = 1 → a * b = b * a) : Subgroup G where
  carrier := {x | x * x = 1}
  one_mem' := by
    change (1 : G) * 1 = 1
    simp
  mul_mem' := by
    intro a b ha hb
    change a * a = 1 at ha
    change b * b = 1 at hb
    change (a * b) * (a * b) = 1
    calc
      (a * b) * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
      _ = a * (a * b) * b := by rw [hcomm a b ha hb]
      _ = (a * a) * (b * b) := by simp only [mul_assoc]
      _ = 1 := by rw [ha, hb]; simp
  inv_mem' := by
    intro a ha
    change a * a = 1 at ha
    change a⁻¹ * a⁻¹ = 1
    rw [involution_inv ha]
    exact ha

end KrebsSankarQ53
