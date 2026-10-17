import KrebsSankarQ53.QuotientLift

/-!
# Extending a Cayley coloring from a subgroup

Left cosets carry translated copies of the subgroup graph. We choose one
representative per coset and use it to extend a coloring to the whole group.
-/

namespace KrebsSankarQ53

variable {G : Type*} [Group G]

/-- The equivalence relation of belonging to the same left coset of `H`. -/
private def leftCosetSetoid (H : Subgroup G) : Setoid G where
  r x y := x⁻¹ * y ∈ H
  iseqv := by
    constructor
    · intro x
      simpa using H.one_mem
    · intro x y hxy
      simpa only [mul_inv_rev, inv_inv] using H.inv_mem hxy
    · intro x y z hxy hyz
      have heq : x⁻¹ * z = (x⁻¹ * y) * (y⁻¹ * z) := by group
      rw [heq]
      exact H.mul_mem hxy hyz

/-- A fixed representative of each left coset. -/
private noncomputable def cosetRep (H : Subgroup G) (g : G) : G :=
  Quotient.out (Quotient.mk (leftCosetSetoid H) g)

private theorem cosetRep_mem (H : Subgroup G) (g : G) :
    (cosetRep H g)⁻¹ * g ∈ H := by
  have hq : Quotient.mk (leftCosetSetoid H) (cosetRep H g) =
      Quotient.mk (leftCosetSetoid H) g :=
    Quotient.out_eq (Quotient.mk (leftCosetSetoid H) g)
  exact Quotient.exact hq

private theorem cosetRep_mul (H : Subgroup G) (g : G) (s : H) :
    cosetRep H (g * s.val) = cosetRep H g := by
  have hq : Quotient.mk (leftCosetSetoid H) (g * s.val) =
      Quotient.mk (leftCosetSetoid H) g := by
    apply Quotient.sound
    change (g * s.val)⁻¹ * g ∈ H
    simpa using H.inv_mem s.property
  exact congrArg Quotient.out hq

private noncomputable def cosetPart (H : Subgroup G) (g : G) : H :=
  ⟨(cosetRep H g)⁻¹ * g, cosetRep_mem H g⟩

private theorem cosetPart_mul (H : Subgroup G) (g : G) (s : H) :
    cosetPart H (g * s.val) = cosetPart H g * s := by
  apply Subtype.ext
  change (cosetRep H (g * s.val))⁻¹ * (g * s.val) =
    ((cosetRep H g)⁻¹ * g) * s.val
  rw [cosetRep_mul]
  group

/-- Regard a set of subgroup elements as a connection set in the whole group. -/
def subgroupConnection (H : Subgroup G) (S : Set H) : Set G :=
  {s | ∃ t : H, t ∈ S ∧ t.val = s}

theorem subgroupConnection_eq_image (H : Subgroup G) (S : Set H) :
    subgroupConnection H S = (Subtype.val '' S) := by
  ext g
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩

theorem subgroupConnection_ncard (H : Subgroup G) (S : Set H) :
    (subgroupConnection H S).ncard = S.ncard := by
  rw [subgroupConnection_eq_image]
  exact Set.ncard_image_of_injective S (fun a b h => Subtype.ext h)

/-- A proper coloring extends across the left cosets. -/
theorem subgroup_color_extend (H : Subgroup G) (S : Set H)
    (n : Nat) (c : H → Fin n) (hc : CayleyProperColoring S c) :
    ∃ C : G → Fin n, CayleyProperColoring (subgroupConnection H S) C := by
  refine ⟨fun g => c (cosetPart H g), ?_⟩
  intro x y hxy
  rcases hxy with ⟨s, hs, rfl⟩
  rcases hs with ⟨t, ht, rfl⟩
  have hp := cosetPart_mul H x t
  change c (cosetPart H x) ≠ c (cosetPart H (x * t.val))
  rw [hp]
  exact hc (cosetPart H x) (cosetPart H x * t) ⟨t, ht, rfl⟩

/-- A two-coloring of the whole graph would restrict to the subgroup. -/
theorem subgroup_no_two_extend (H : Subgroup G) (S : Set H)
    (hnotwo : ¬ ∃ c : H → Fin 2, CayleyProperColoring S c) :
    ¬ ∃ C : G → Fin 2,
      CayleyProperColoring (subgroupConnection H S) C := by
  rintro ⟨C, hC⟩
  apply hnotwo
  refine ⟨fun x => C x.val, ?_⟩
  intro x y hxy
  rcases hxy with ⟨s, hs, rfl⟩
  exact hC x.val (x * s).val ⟨s.val, ⟨s, hs, rfl⟩, rfl⟩

/-- The quotient result extends to a dihedral section of the ambient group. -/
theorem d8_section_has_three_chromatic_cayley
    (H : Subgroup G) (f : H →* D8) (hf : Function.Surjective f) :
    ∃ S : Set G, S.Finite ∧ S.ncard ≤ 10 ∧
      (∃ c : G → Fin 3, CayleyProperColoring S c) ∧
      ¬ ∃ c : G → Fin 2, CayleyProperColoring S c := by
  rcases d8_quotient_has_three_chromatic_cayley f hf with
    ⟨S, hfinite, hcard, ⟨c, hc⟩, hn⟩
  have hfiniteG : (subgroupConnection H S).Finite := by
    rw [subgroupConnection_eq_image]
    exact hfinite.image Subtype.val
  have hcardG : (subgroupConnection H S).ncard ≤ 10 := by
    rw [subgroupConnection_ncard]
    exact hcard
  exact ⟨subgroupConnection H S,
    hfiniteG, hcardG,
    subgroup_color_extend H S 3 c hc, subgroup_no_two_extend H S hn⟩

end KrebsSankarQ53
