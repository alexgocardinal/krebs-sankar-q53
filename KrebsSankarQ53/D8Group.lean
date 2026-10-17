import KrebsSankarQ53.Witness
import KrebsSankarQ53.CycleLift

/-!
# The finite witness as a separate group type

`Fin 8` has other algebraic operations in mathlib. A separate type prevents
its multiplication from being confused with the dihedral table in `Witness`.
-/

namespace KrebsSankarQ53

/-- The eight vertices, with multiplication supplied by the checked table. -/
structure D8 where
  val : Fin 8
  deriving DecidableEq

/-- Two wrapped vertices are equal when their original labels are equal. -/
theorem D8.ext {a b : D8} (h : a.val = b.val) : a = b := by
  cases a with
  | mk x =>
    cases b with
    | mk y => exact congrArg D8.mk h

noncomputable instance : Group D8 where
  mul x y := ⟨dmul x.val y.val⟩
  one := ⟨0⟩
  inv x := ⟨Classical.choose (dmul_inverses x.val)⟩
  div x y := ⟨dmul x.val (Classical.choose (dmul_inverses y.val))⟩
  mul_assoc x y z := by
    apply D8.ext
    exact dmul_assoc x.val y.val z.val
  one_mul x := by
    apply D8.ext
    exact dmul_one_left x.val
  mul_one x := by
    apply D8.ext
    exact dmul_one_right x.val
  inv_mul_cancel x := by
    apply D8.ext
    exact (Classical.choose_spec (dmul_inverses x.val)).2
  div_eq_mul_inv x y := rfl

def d8Connection : Set D8 := {s | s.val ∈ generators}

theorem d8_rightCayleyAdj_iff (u v : D8) :
    rightCayleyAdj d8Connection u v ↔ cayAdj u.val v.val := by
  constructor
  · rintro ⟨s, hs, hv⟩
    exact ⟨s.val, hs, congrArg D8.val hv⟩
  · rintro ⟨s, hs, hv⟩
    refine ⟨⟨s⟩, hs, ?_⟩
    apply D8.ext
    exact hv

theorem d8_threeColor_proper :
    CayleyProperColoring d8Connection (fun v => threeColor v.val) := by
  intro u v huv
  exact threeColor_proper u.val v.val
    ((adj_iff_cayAdj u.val v.val).mpr ((d8_rightCayleyAdj_iff u v).mp huv))

theorem d8Connection_inv_mem {s : D8} (hs : s ∈ d8Connection) :
    s⁻¹ ∈ d8Connection := by
  have hsq : s * s = 1 := by
    apply D8.ext
    exact generators_are_involutions s.val hs
  have hinv_eq : s⁻¹ = s := by
    calc
      s⁻¹ = s⁻¹ * (s * s) := by rw [hsq]; simp
      _ = (s⁻¹ * s) * s := by rw [mul_assoc]
      _ = s := by simp
  simpa [hinv_eq] using hs

theorem d8_fiveCycle_edges :
    rightCayleyAdj d8Connection ⟨0⟩ ⟨2⟩ ∧
    rightCayleyAdj d8Connection ⟨2⟩ ⟨6⟩ ∧
    rightCayleyAdj d8Connection ⟨6⟩ ⟨1⟩ ∧
    rightCayleyAdj d8Connection ⟨1⟩ ⟨5⟩ ∧
    rightCayleyAdj d8Connection ⟨5⟩ ⟨0⟩ := by
  rcases fiveCycle with ⟨h₀, h₁, h₂, h₃, h₄⟩
  exact ⟨(d8_rightCayleyAdj_iff ⟨0⟩ ⟨2⟩).mpr ((adj_iff_cayAdj 0 2).mp h₀),
    (d8_rightCayleyAdj_iff ⟨2⟩ ⟨6⟩).mpr ((adj_iff_cayAdj 2 6).mp h₁),
    (d8_rightCayleyAdj_iff ⟨6⟩ ⟨1⟩).mpr ((adj_iff_cayAdj 6 1).mp h₂),
    (d8_rightCayleyAdj_iff ⟨1⟩ ⟨5⟩).mpr ((adj_iff_cayAdj 1 5).mp h₃),
    (d8_rightCayleyAdj_iff ⟨5⟩ ⟨0⟩).mpr ((adj_iff_cayAdj 5 0).mp h₄)⟩

end KrebsSankarQ53
