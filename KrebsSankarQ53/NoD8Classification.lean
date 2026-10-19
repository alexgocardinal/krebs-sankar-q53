import KrebsSankarQ53.ElementaryComplement

namespace KrebsSankarQ53

universe u

/-- The structural implication, with no finiteness assumption. -/
theorem no_d8_section_quaternion_product
    {G : Type u} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) (i j : G) (hne : i * j ≠ j * i) :
    ∃ (E : Type u) (_ : CommGroup E),
      (∀ e : E, e * e = 1) ∧ Nonempty (G ≃* (QuaternionGroup 2 × E)) := by
  classical
  let hcomm := no_d8_section_involutions_commute hG hno
  let T := involutionSubgroup hcomm
  letI : CommGroup T :=
    { (inferInstance : Group T) with mul_comm := involutionSubgroup_mul_comm hcomm }
  have hT : ∀ t : T, t * t = 1 := by
    intro t
    apply Subtype.ext
    exact t.property
  have hp := no_d8_section_noncommuting_pair_square_identity hG hno i j hne
  let z : T := ⟨i ^ 2, square_is_involution hG i⟩
  have hz : z ≠ 1 := by
    intro he
    exact hp.2.2.2 (congrArg Subtype.val he)
  obtain ⟨E, hzE, hsplit⟩ := elementaryAbelian_exists_complement hT z hz
  have ho : orderOf i = 4 := order_four_of_fourth_one_square_ne_one (hG i) hp.2.2.2
  have hc := no_d8_section_pair_conjugation hG hno i j hne
  let f := q8PairHom i j ho hp.1.symm hc
  have hf : Function.Injective f := q8PairHom_injective i j ho hp.1.symm hc hne
  have hrange : f.range = Subgroup.closure ({i, j} : Set G) :=
    q8PairHom_range i j ho hp.1.symm hc
  have hfz : f (QuaternionGroup.a 2) = (z : G) := by
    norm_num [f, q8PairHom, q8Word, q8Power, z]
  let F : QuaternionGroup 2 × E →* G :=
    { toFun := fun x => f x.1 * ((x.2 : T) : G)
      map_one' := by simp
      map_mul' := by
        rintro ⟨q, e⟩ ⟨r, d⟩
        change f (q * r) * (((e : T) : G) * ((d : T) : G)) =
          (f q * ((e : T) : G)) * (f r * ((d : T) : G))
        rw [map_mul]
        have he := no_d8_section_involutions_central hG hno (f r)
          ((e : T) : G) (e : T).property
        calc
          (f q * f r) * (((e : T) : G) * ((d : T) : G)) =
            f q * (f r * ((e : T) : G)) * ((d : T) : G) := by group
          _ = (f q * ((e : T) : G)) * (f r * ((d : T) : G)) := by rw [he]; group }
  have hker : ∀ x, F x = 1 → x = 1 := by
    rintro ⟨q, e⟩ he
    change f q * ((e : T) : G) = 1 at he
    have hfe : f q = (((e : T) : G))⁻¹ := by
      calc
        f q = (f q * ((e : T) : G)) * (((e : T) : G))⁻¹ := by group
        _ = (((e : T) : G))⁻¹ := by rw [he]; simp
    have hq2 : q * q = 1 := by
      apply hf
      rw [map_mul, map_one, hfe, involution_inv (e : T).property]
      exact (e : T).property
    have hposs : ∀ q : QuaternionGroup 2, q * q = 1 →
        q = 1 ∨ q = QuaternionGroup.a 2 := by decide
    rcases hposs q hq2 with hq | hq
    · subst q
      rw [map_one, one_mul] at he
      apply Prod.ext rfl
      apply Subtype.ext
      apply Subtype.ext
      exact he
    · have hze : z = (e : T)⁻¹ := by
        apply Subtype.ext
        exact hfz.symm.trans (by simpa only [hq] using hfe)
      exact False.elim (hzE (by rw [hze]; exact E.inv_mem e.property))
  have hinj : Function.Injective F := by
    intro a b hab
    have hzero : F (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab]; group
    exact inv_mul_eq_one.mp (hker _ hzero)
  have hsurj : Function.Surjective F := by
    intro g
    obtain ⟨k, hk, t, ht, _, hg⟩ := no_d8_section_quaternion_center_cover hG hno i j hne g
    have hkf : k ∈ f.range := by rw [hrange]; exact hk
    obtain ⟨q, hq⟩ := hkf
    let tT : T := ⟨t, ht⟩
    obtain ⟨e, he, hte | hte⟩ := hsplit tT
    · refine ⟨(q, ⟨e, he⟩), ?_⟩
      change f q * (e : G) = g
      calc
        f q * (e : G) = k * t := by rw [hq, ← congrArg Subtype.val hte]
        _ = g := hg.symm
    · refine ⟨(q * QuaternionGroup.a 2, ⟨e, he⟩), ?_⟩
      change f (q * QuaternionGroup.a 2) * (e : G) = g
      calc
        f (q * QuaternionGroup.a 2) * (e : G) = k * ((z : G) * (e : G)) := by
          rw [map_mul, hfz, hq]; group
        _ = k * t := by rw [← congrArg Subtype.val hte]
        _ = g := hg.symm
  refine ⟨E, inferInstance, ?_, ⟨(MulEquiv.ofBijective F ⟨hinj, hsurj⟩).symm⟩⟩
  intro e
  apply Subtype.ext
  exact hT (e : T)

end KrebsSankarQ53
