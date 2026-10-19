import KrebsSankarQ53.NoD8Classification
import KrebsSankarQ53.QuaternionCubelike
import KrebsSankarQ53.D8FiveLift

/-!
# Krebs–Sankar Q5.3: exact classification and a ten-element witness

The connection sets are inverse-closed and omit the identity. Graphs
need not be connected; groups and elementary abelian factors may be
infinite. All algebraic and coloring inputs are proved in this library.
-/

namespace KrebsSankarQ53

universe u

def IsExactThreeCayleyConnection {G : Type*} [Group G] (S : Set G) : Prop :=
  (∀ s ∈ S, s⁻¹ ∈ S) ∧ 1 ∉ S ∧
    (∃ c : G → Fin 3, CayleyProperColoring S c) ∧
      ¬ ∃ c : G → Fin 2, CayleyProperColoring S c

def HasExactThreeCayley (G : Type*) [Group G] : Prop :=
  ∃ S : Set G, IsExactThreeCayleyConnection S

def IsQuaternionElementaryProduct (G : Type u) [Group G] : Prop :=
  ∃ (E : Type u) (_ : CommGroup E),
    (∀ e : E, e * e = 1) ∧ Nonempty (G ≃* (QuaternionGroup 2 × E))

theorem cayleyColor_symmetrize {G : Type*} [Group G]
    (S : Set G) {n : ℕ} (c : G → Fin n) (hc : CayleyProperColoring S c) :
    CayleyProperColoring (S ∪ Inv.inv '' S) c := by
  intro x y hxy
  rcases hxy with ⟨s, hs, rfl⟩
  rcases hs with hs | ⟨t, ht, rfl⟩
  · exact hc x (x * s) ⟨s, hs, rfl⟩
  · exact (hc (x * t⁻¹) x ⟨t, ht, by group⟩).symm

theorem d8_section_exact_three_card_le_ten
    {G : Type*} [Group G] (hG : ExponentFour G) (hD : HasD8Section G) :
    ∃ S : Set G, S.Finite ∧ S.ncard ≤ 10 ∧ IsExactThreeCayleyConnection S := by
  rcases hD with ⟨H, f, hf⟩
  obtain ⟨S, hfin, hcard, ⟨c, hc⟩, hn⟩ :=
    d8_section_has_three_chromatic_cayley_five hG H f hf
  let T : Set G := S ∪ Inv.inv '' S
  have hcT : CayleyProperColoring T c := cayleyColor_symmetrize S c hc
  have hfinT : T.Finite := hfin.union (hfin.image Inv.inv)
  have hcardT : T.ncard ≤ 10 := by
    have hi : (Inv.inv '' S).ncard = S.ncard :=
      Set.ncard_image_of_injective S inv_injective
    have hu := Set.ncard_union_le S (Inv.inv '' S)
    change (S ∪ Inv.inv '' S).ncard ≤ 10
    rw [hi] at hu
    omega
  refine ⟨T, hfinT, hcardT, ?_, ?_, ⟨c, hcT⟩, ?_⟩
  · intro s hs
    rcases hs with hs | ⟨t, ht, rfl⟩
    · exact Or.inr ⟨s, hs, rfl⟩
    · exact Or.inl (by simpa only [inv_inv] using ht)
  · intro h1
    exact hcT 1 1 ⟨1, h1, by simp⟩ rfl
  · rintro ⟨b, hb⟩
    apply hn
    refine ⟨b, ?_⟩
    intro x y hxy
    rcases hxy with ⟨s, hs, hy⟩
    exact hb x y ⟨s, Or.inl hs, hy⟩

theorem quaternionElementaryProduct_no_exact_three
    {G : Type u} [Group G] (hQ : IsQuaternionElementaryProduct G) :
    ¬ HasExactThreeCayley G := by
  rcases hQ with ⟨E, instE, hE, ⟨e⟩⟩
  letI := instE
  rintro ⟨S, hS, _, ⟨c, hc⟩, hn⟩
  let T : Set (QuaternionGroup 2 × E) := e '' S
  have hT : ∀ t ∈ T, t⁻¹ ∈ T := by
    rintro t ⟨s, hs, rfl⟩
    exact ⟨s⁻¹, hS s hs, map_inv e s⟩
  have hback : ∀ t ∈ T, e.symm t ∈ S := by
    rintro t ⟨s, hs, rfl⟩
    simpa only [e.symm_apply_apply] using hs
  have hct : CayleyProperColoring T (fun t => c (e.symm t)) :=
    cayleyColor_pullback e.symm.toMonoidHom T S 3 hback c hc
  obtain ⟨d, hd⟩ := quaternionProduct_cayley_three_implies_two hE T hT _ hct
  apply hn
  exact ⟨fun x => d (e x), cayleyColor_pullback e.toMonoidHom S T 2
    (fun s hs => ⟨s, hs, rfl⟩) d hd⟩

/-- The exact theorem for every nonabelian exponent-four group,
including infinite groups and disconnected Cayley graphs. -/
theorem q53_full_classification
    {G : Type u} [Group G] (hG : ExponentFour G)
    (hnonabelian : ∃ i j : G, i * j ≠ j * i) :
    (HasExactThreeCayley G ↔ HasD8Section G) ∧
      (HasD8Section G ↔ ¬ IsQuaternionElementaryProduct G) ∧
        (HasD8Section G → ∃ S : Set G,
          S.Finite ∧ S.ncard ≤ 10 ∧ IsExactThreeCayleyConnection S) := by
  have hpositive : HasD8Section G → HasExactThreeCayley G := by
    intro hD
    obtain ⟨S, _, _, hS⟩ := d8_section_exact_three_card_le_ten hG hD
    exact ⟨S, hS⟩
  have hnegative : ¬ HasD8Section G → IsQuaternionElementaryProduct G := by
    intro hno
    obtain ⟨i, j, hne⟩ := hnonabelian
    exact no_d8_section_quaternion_product hG hno i j hne
  refine ⟨⟨?_, hpositive⟩, ⟨?_, ?_⟩, d8_section_exact_three_card_le_ten hG⟩
  · intro hthree
    by_contra hno
    exact quaternionElementaryProduct_no_exact_three (hnegative hno) hthree
  · intro hD hQ
    exact quaternionElementaryProduct_no_exact_three hQ (hpositive hD)
  · intro hnotQ
    by_contra hno
    exact hnotQ (hnegative hno)

end KrebsSankarQ53
