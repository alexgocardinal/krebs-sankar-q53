import KrebsSankarQ53.LocalSquareQuotient

/-!
# Passing D8 sections through subgroups and quotients

These two lemmas make the definition of a section usable in the
local square quotient argument. Both transfers construct a subgroup
of the original group and a surjective homomorphism from it to D8.
-/

namespace KrebsSankarQ53

theorem hasD8Section_of_subgroup
    {G : Type*} [Group G] (H : Subgroup G)
    (h : HasD8Section H) : HasD8Section G := by
  rcases h with ⟨K, f, hf⟩
  let P : Subgroup G := Subgroup.map H.subtype K
  have hmem (z : P) : (z : G) ∈ H := by
    rcases z.property with ⟨y, hy, hzy⟩
    rw [← hzy]
    exact y.property
  let r : P →* K :=
    { toFun := fun z =>
        ⟨⟨(z : G), hmem z⟩, by
          rcases z.property with ⟨y, hy, hzy⟩
          have heq : (⟨(z : G), hmem z⟩ : H) = y :=
            Subtype.ext hzy.symm
          rw [heq]
          exact hy⟩
      map_one' := by apply Subtype.ext; apply Subtype.ext; rfl
      map_mul' := by
        intro a b
        apply Subtype.ext
        apply Subtype.ext
        rfl }
  refine ⟨P, f.comp r, ?_⟩
  intro d
  rcases hf d with ⟨k, hk⟩
  have hp : (k : G) ∈ P := by
    change ∃ y : H, y ∈ K ∧ (H.subtype y : G) = (k : G)
    exact ⟨(k : H), k.property, rfl⟩
  refine ⟨⟨(k : G), hp⟩, ?_⟩
  change f (r ⟨(k : G), hp⟩) = d
  rw [show r ⟨(k : G), hp⟩ = k from Subtype.ext (Subtype.ext rfl)]
  exact hk

theorem hasD8Section_of_quotient
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (h : HasD8Section (G ⧸ N)) : HasD8Section G := by
  rcases h with ⟨K, f, hf⟩
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let P : Subgroup G := Subgroup.comap q K
  let r : P →* K :=
    { toFun := fun z => ⟨q (z : G), z.property⟩
      map_one' := by apply Subtype.ext; exact map_one q
      map_mul' := by
        intro a b
        apply Subtype.ext
        change q ((a : G) * (b : G)) = q (a : G) * q (b : G)
        exact map_mul q (a : G) (b : G) }
  refine ⟨P, f.comp r, ?_⟩
  intro d
  rcases hf d with ⟨k, hk⟩
  rcases QuotientGroup.mk'_surjective N (k : G ⧸ N) with ⟨y, hy⟩
  have hp : y ∈ P := by
    change q y ∈ K
    rw [hy]
    exact k.property
  refine ⟨⟨y, hp⟩, ?_⟩
  change f (r ⟨y, hp⟩) = d
  rw [show r ⟨y, hp⟩ = k from Subtype.ext hy]
  exact hk

end KrebsSankarQ53
