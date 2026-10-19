import KrebsSankarQ53.CubelikeObstruction
import KrebsSankarQ53.QuaternionPair

/-!
# Every undirected Cayley graph on Q8 × E is cubelike

The explicit coordinate bijection replaces a quaternion by two quotient
bits and a sign bit. A coordinate difference corresponds to either the
original group difference or its inverse. Inverse-closed connection sets
therefore give exactly the same edges. The exponent-two obstruction then
applies to arbitrary E, without a finite-connection-set restriction.
-/

namespace KrebsSankarQ53

abbrev Q8Coordinates := ZMod 2 × ZMod 2 × ZMod 2

def q8Coordinates : QuaternionGroup 2 ≃ Q8Coordinates where
  toFun
    | .a a => ((a.val % 2 : ℕ), 0, (a.val / 2 : ℕ))
    | .xa a => ((a.val % 2 : ℕ), 1, (a.val / 2 : ℕ))
  invFun p := if p.2.1 = 0 then
    .a (p.1.val + 2 * p.2.2.val : ℕ) else
    .xa (p.1.val + 2 * p.2.2.val : ℕ)
  left_inv := by rintro (a | a) <;> fin_cases a <;> decide
  right_inv := by
    rintro ⟨a, b, c⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

/-- This is an ordinary kernel-checked calculation on the 64 pairs. -/
theorem q8Coordinates_difference (x y : QuaternionGroup 2) :
    q8Coordinates.symm (q8Coordinates y - q8Coordinates x) = x⁻¹ * y ∨
      q8Coordinates.symm (q8Coordinates y - q8Coordinates x) = (x⁻¹ * y)⁻¹ := by
  revert x y
  decide

theorem quaternionProduct_cayley_three_implies_two
    {E : Type*} [CommGroup E] (hE : ∀ e : E, e * e = 1)
    (S : Set (QuaternionGroup 2 × E))
    (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (c : QuaternionGroup 2 × E → Fin 3) (hc : CayleyProperColoring S c) :
    ∃ b : QuaternionGroup 2 × E → Fin 2, CayleyProperColoring S b := by
  classical
  let V := Multiplicative Q8Coordinates × E
  let φ : (QuaternionGroup 2 × E) ≃ V :=
    { toFun := fun x => (Multiplicative.ofAdd (q8Coordinates x.1), x.2)
      invFun := fun x => (q8Coordinates.symm (Multiplicative.toAdd x.1), x.2)
      left_inv := by intro x; exact Prod.ext (q8Coordinates.symm_apply_apply x.1) rfl
      right_inv := by intro x; exact Prod.ext (q8Coordinates.apply_symm_apply _) rfl }
  have hV : ∀ v : V, v * v = 1 := by
    intro v
    apply Prod.ext
    · change (Multiplicative.toAdd v.1) + (Multiplicative.toAdd v.1) = 0
      have hbits : ∀ a : Q8Coordinates, a + a = 0 := by decide
      exact hbits _
    · exact hE v.2
  have hdiff (x y : QuaternionGroup 2 × E) :
      φ.symm ((φ x)⁻¹ * φ y) = x⁻¹ * y ∨
        φ.symm ((φ x)⁻¹ * φ y) = (x⁻¹ * y)⁻¹ := by
    change (q8Coordinates.symm (-q8Coordinates x.1 + q8Coordinates y.1), x.2⁻¹ * y.2) =
        x⁻¹ * y ∨
      (q8Coordinates.symm (-q8Coordinates x.1 + q8Coordinates y.1), x.2⁻¹ * y.2) =
        (x⁻¹ * y)⁻¹
    have he : -q8Coordinates x.1 + q8Coordinates y.1 =
        q8Coordinates y.1 - q8Coordinates x.1 := by abel
    rw [he]
    rcases q8Coordinates_difference x.1 y.1 with h | h
    · exact Or.inl (Prod.ext h rfl)
    · right
      apply Prod.ext h
      change x.2⁻¹ * y.2 = (x.2⁻¹ * y.2)⁻¹
      exact (involution_inv (hE (x.2⁻¹ * y.2))).symm
  have hdiff' (x : QuaternionGroup 2 × E) (v : V) :
      φ.symm v = x⁻¹ * φ.symm (φ x * v) ∨
        φ.symm v = (x⁻¹ * φ.symm (φ x * v))⁻¹ := by
    have h := hdiff x (φ.symm (φ x * v))
    have hcancel : (φ x)⁻¹ * (φ x * v) = v := by
      rw [← mul_assoc, inv_mul_cancel, one_mul]
    simpa only [φ.apply_symm_apply, hcancel] using h
  let T : Set V := φ '' S
  have hct : CayleyProperColoring T (fun v => c (φ.symm v)) := by
    intro x y hxy
    rcases hxy with ⟨v, ⟨s, hs, rfl⟩, rfl⟩
    let a := φ.symm x
    let b := φ.symm (x * φ s)
    have hx : φ a = x := φ.apply_symm_apply x
    have hb : φ.symm (φ a * φ s) = b := by rw [hx]
    have hh := hdiff' a (φ s)
    rw [φ.symm_apply_apply, hb] at hh
    have hmem : a⁻¹ * b ∈ S := by
      rcases hh with hh | hh
      · rw [← hh]; exact hs
      · have heq : a⁻¹ * b = s⁻¹ := by rw [hh, inv_inv]
        rw [heq]
        exact hS s hs
    exact hc a b ⟨a⁻¹ * b, hmem, by group⟩
  obtain ⟨d, hd⟩ := elementaryAbelian_cayley_three_implies_two hV T _ hct
  refine ⟨fun x => d (φ x), ?_⟩
  intro x y hxy
  rcases hxy with ⟨s, hs, rfl⟩
  let v := (φ x)⁻¹ * φ (x * s)
  have hv : v ∈ T := by
    have hh := hdiff x (x * s)
    have hcancel : x⁻¹ * (x * s) = s := by group
    rw [hcancel] at hh
    rcases hh with hh | hh
    · exact ⟨s, hs, by rw [← hh]; exact φ.apply_symm_apply _⟩
    · exact ⟨s⁻¹, hS s hs, by rw [← hh]; exact φ.apply_symm_apply _⟩
  exact hd (φ x) (φ (x * s)) ⟨v, hv, by
    dsimp [v]
    rw [← mul_assoc, mul_inv_cancel, one_mul]⟩

end KrebsSankarQ53
