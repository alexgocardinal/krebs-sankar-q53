import KrebsSankarQ53.DihedralCosets

/-!
# Normal forms for two involutions

Write `r = a*b` for involutions `a,b`. Conjugation by `a` inverts every
power of `r`. Hence the rotations and their reflected coset form a subgroup.
When `r` has order four and `a` lies outside the rotations, this subgroup
has the eight normal forms of D8; identifying it with the explicit D8 type
is a subsequent step.
-/

namespace KrebsSankarQ53

/-- Conjugation by either generating reflection preserves the rotation
subgroup. -/
theorem involution_conjugates_rotation_mem
    {G : Type*} [Group G] {a b : G}
    (ha : a * a = 1) (hb : b * b = 1)
    (x : Subgroup.zpowers (a * b)) :
    a * (x : G) * a⁻¹ ∈ Subgroup.zpowers (a * b) := by
  let r := a * b
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.property
  have ha_inv : a⁻¹ = a := involution_inv ha
  have hbase : a * r * a⁻¹ = r⁻¹ := by
    simpa only [r, ha_inv] using involution_reflects_product ha hb
  have hpow : a * r ^ k * a⁻¹ = (r ^ k)⁻¹ := by
    calc
      a * r ^ k * a⁻¹ = (a * r * a⁻¹) ^ k := (conj_zpow).symm
      _ = (r⁻¹) ^ k := by rw [hbase]
      _ = (r ^ k)⁻¹ := by simp
  rw [← hk]
  rw [hpow]
  exact (Subgroup.zpowers r).inv_mem
    (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)

/-- The rotations and the right coset obtained by multiplying by `a`
form a subgroup. -/
def dihedralNormalFormSubgroup
    {G : Type*} [Group G] (a b : G)
    (ha : a * a = 1) (hb : b * b = 1) : Subgroup G := by
  let R : Subgroup G := Subgroup.zpowers (a * b)
  refine
    { carrier := {x | x ∈ R ∨ ∃ t : R, x = (t : G) * a}
      one_mem' := ?_
      mul_mem' := ?_
      inv_mem' := ?_ }
  · intro x y hx hy
    rcases hx with hx | ⟨t, rfl⟩
    · rcases hy with hy | ⟨u, rfl⟩
      · exact Or.inl (R.mul_mem hx hy)
      · right
        refine ⟨⟨x * (u : G), R.mul_mem hx u.property⟩, ?_⟩
        change x * ((u : G) * a) = (x * (u : G)) * a
        exact (mul_assoc x (u : G) a).symm
    · rcases hy with hy | ⟨u, rfl⟩
      · have hconj : a * y * a⁻¹ ∈ R :=
          involution_conjugates_rotation_mem ha hb ⟨y, hy⟩
        right
        refine ⟨⟨(t : G) * (a * y * a⁻¹),
          R.mul_mem t.property hconj⟩, ?_⟩
        change ((t : G) * a) * y =
          ((t : G) * (a * y * a⁻¹)) * a
        group
      · have hconj : a * (u : G) * a⁻¹ ∈ R :=
          involution_conjugates_rotation_mem ha hb u
        left
        have heq : ((t : G) * a) * ((u : G) * a) =
            (t : G) * (a * (u : G) * a⁻¹) := by
          calc
            ((t : G) * a) * ((u : G) * a) =
                (t : G) * (a * (u : G) * a⁻¹) * (a * a) := by group
            _ = (t : G) * (a * (u : G) * a⁻¹) := by rw [ha]; simp
        rw [heq]
        exact R.mul_mem t.property hconj
  · exact Or.inl R.one_mem
  · intro x hx
    rcases hx with hx | ⟨t, rfl⟩
    · exact Or.inl (R.inv_mem hx)
    · have hconj : a * (t : G)⁻¹ * a⁻¹ ∈ R :=
        involution_conjugates_rotation_mem ha hb
          ⟨(t : G)⁻¹, R.inv_mem t.property⟩
      right
      refine ⟨⟨a * (t : G)⁻¹ * a⁻¹, hconj⟩, ?_⟩
      change ((t : G) * a)⁻¹ =
        (a * (t : G)⁻¹ * a⁻¹) * a
      calc
        ((t : G) * a)⁻¹ = a⁻¹ * (t : G)⁻¹ := mul_inv_rev _ _
        _ = a * (t : G)⁻¹ := by rw [involution_inv ha]
        _ = (a * (t : G)⁻¹ * a⁻¹) * a := by group

end KrebsSankarQ53
