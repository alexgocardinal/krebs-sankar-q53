import KrebsSankarQ53.QuaternionCentralizer
import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# A quaternion subgroup from every noncommuting pair

The pair square identity gives the standard presentation of Q8.
We evaluate Mathlib's `QuaternionGroup 2` in the pair and prove that
the resulting map is an isomorphism onto their generated subgroup.
-/

namespace KrebsSankarQ53

theorem order_four_of_fourth_one_square_ne_one
    {G : Type*} [Group G] {i : G} (h4 : i ^ 4 = 1) (h2 : i ^ 2 ≠ 1) :
    orderOf i = 4 := by
  apply (orderOf_eq_iff (by decide : 0 < 4)).2
  refine ⟨h4, ?_⟩
  intro m hm hpos hp
  have hm' : m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hm' with rfl | rfl | rfl
  · have hi : i = 1 := by simpa only [pow_one] using hp
    exact h2 (by rw [hi]; exact one_pow 2)
  · exact h2 hp
  · have hi : i = 1 := by
      calc
        i = i ^ 3 * i := by rw [hp]; simp
        _ = i ^ 4 := (pow_succ i 3).symm
        _ = 1 := h4
    exact h2 (by rw [hi]; simp)

def q8Power {G : Type*} [Group G] (i : G) (a : ZMod 4) : G := i ^ a.val

theorem q8Power_zero {G : Type*} [Group G] (i : G) : q8Power i 0 = 1 := by
  simp [q8Power]

theorem q8Power_add {G : Type*} [Group G] (i : G) (ho : orderOf i = 4)
    (a b : ZMod 4) : q8Power i (a + b) = q8Power i a * q8Power i b := by
  simp only [q8Power, ZMod.val_add]
  have hm := pow_mod_orderOf i (a.val + b.val)
  rw [ho] at hm
  exact hm.trans (pow_add i a.val b.val)

theorem q8Power_neg {G : Type*} [Group G] (i : G) (ho : orderOf i = 4)
    (a : ZMod 4) : q8Power i (-a) = (q8Power i a)⁻¹ := by
  have he : q8Power i a * q8Power i (-a) = 1 := by
    rw [← q8Power_add i ho, add_neg_cancel, q8Power_zero]
  calc
    q8Power i (-a) = (q8Power i a)⁻¹ * (q8Power i a * q8Power i (-a)) := by group
    _ = (q8Power i a)⁻¹ := by rw [he]; simp

theorem q8Power_sub {G : Type*} [Group G] (i : G) (ho : orderOf i = 4)
    (a b : ZMod 4) : q8Power i (a - b) = q8Power i a * (q8Power i b)⁻¹ := by
  rw [sub_eq_add_neg, q8Power_add i ho, q8Power_neg i ho]

theorem q8Power_injective {G : Type*} [Group G] (i : G) (ho : orderOf i = 4) :
    Function.Injective (q8Power i) := by
  intro a b he
  apply ZMod.val_injective 4
  have hm := (pow_eq_pow_iff_modEq).1 he
  change a.val % orderOf i = b.val % orderOf i at hm
  simpa only [ho, Nat.mod_eq_of_lt (ZMod.val_lt a),
    Nat.mod_eq_of_lt (ZMod.val_lt b)] using hm

theorem no_d8_section_pair_conjugation
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) (i j : G) (hne : i * j ≠ j * i) :
    j * i * j⁻¹ = i⁻¹ := by
  have hc := no_d8_section_noncommuting_commutator_eq_square hG hno j i (Ne.symm hne)
  have hs := (no_d8_section_noncommuting_pair_square_identity hG hno i j hne).1
  have he : j * i * j⁻¹ = i ^ 2 * i := by
    calc
      j * i * j⁻¹ = commutatorTerm j i * i := by dsimp [commutatorTerm]; group
      _ = i ^ 2 * i := by rw [hc, ← hs]
  calc
    j * i * j⁻¹ = i ^ 2 * i := he
    _ = i⁻¹ := by
      have h4 := hG i
      have hp : (i ^ 2 * i) * i = 1 := by simpa only [← pow_succ] using h4
      calc
        i ^ 2 * i = ((i ^ 2 * i) * i) * i⁻¹ := by group
        _ = i⁻¹ := by rw [hp]; simp

theorem q8Power_move {G : Type*} [Group G] (i j : G)
    (ho : orderOf i = 4) (hc : j * i * j⁻¹ = i⁻¹) (a : ZMod 4) :
    q8Power i a * j = j * q8Power i (-a) := by
  have hp : j * q8Power i a * j⁻¹ = (q8Power i a)⁻¹ := by
    change j * i ^ a.val * j⁻¹ = (i ^ a.val)⁻¹
    rw [← conj_pow, hc, inv_pow]
  rw [q8Power_neg i ho]
  calc
    q8Power i a * j = ((q8Power i a)⁻¹)⁻¹ * j := by simp
    _ = (j * q8Power i a * j⁻¹)⁻¹ * j := by rw [hp]
    _ = j * (q8Power i a)⁻¹ := by group

def q8Word {G : Type*} [Group G] (i j : G) : QuaternionGroup 2 → G
  | .a a => q8Power i a
  | .xa a => j * q8Power i a

def q8PairHom {G : Type*} [Group G] (i j : G) (ho : orderOf i = 4)
    (hs : j ^ 2 = i ^ 2) (hc : j * i * j⁻¹ = i⁻¹) : QuaternionGroup 2 →* G where
  toFun := q8Word i j
  map_one' := q8Power_zero i
  map_mul' := by
    rintro (a | a) (b | b)
    · exact q8Power_add i ho a b
    · change j * q8Power i (b - a) = q8Power i a * (j * q8Power i b)
      rw [q8Power_sub i ho]
      calc
        j * (q8Power i b * (q8Power i a)⁻¹) =
            j * ((q8Power i a)⁻¹ * q8Power i b) := by
          have hh : Commute (q8Power i b) (q8Power i a) :=
            (Commute.refl i).pow_pow b.val a.val
          rw [hh.inv_right.eq]
        _ = (j * q8Power i (-a)) * q8Power i b := by rw [q8Power_neg i ho]; group
        _ = q8Power i a * (j * q8Power i b) := by rw [← q8Power_move i j ho hc]; group
    · change j * q8Power i (a + b) = (j * q8Power i a) * q8Power i b
      rw [q8Power_add i ho]
      group
    · change q8Power i (2 + b - a) = (j * q8Power i a) * (j * q8Power i b)
      rw [q8Power_sub i ho, q8Power_add i ho]
      have htwo : q8Power i 2 = j ^ 2 := by simpa [q8Power] using hs.symm
      rw [htwo]
      calc
        j ^ 2 * q8Power i b * (q8Power i a)⁻¹ =
            j ^ 2 * ((q8Power i a)⁻¹ * q8Power i b) := by
          have hh : Commute (q8Power i b) (q8Power i a) :=
            (Commute.refl i).pow_pow b.val a.val
          rw [mul_assoc, hh.inv_right.eq]
        _ = j * (j * q8Power i (-a)) * q8Power i b := by
          rw [q8Power_neg i ho]
          simp only [pow_two]
          group
        _ = (j * q8Power i a) * (j * q8Power i b) := by
          rw [← q8Power_move i j ho hc]; group

theorem q8Word_cross_ne {G : Type*} [Group G] (i j : G)
    (hne : i * j ≠ j * i) (a b : ZMod 4) :
    q8Power i a ≠ j * q8Power i b := by
  intro he
  have hj : j = q8Power i a * (q8Power i b)⁻¹ := by
    calc
      j = (j * q8Power i b) * (q8Power i b)⁻¹ := by group
      _ = q8Power i a * (q8Power i b)⁻¹ := by rw [he]
  apply hne
  rw [hj]
  exact (((Commute.refl i).pow_right a.val).mul_right
    ((Commute.refl i).pow_right b.val).inv_right).eq

theorem q8PairHom_injective {G : Type*} [Group G] (i j : G)
    (ho : orderOf i = 4) (hs : j ^ 2 = i ^ 2)
    (hc : j * i * j⁻¹ = i⁻¹) (hne : i * j ≠ j * i) :
    Function.Injective (q8PairHom i j ho hs hc) := by
  rintro (a | a) (b | b) he
  · exact congrArg QuaternionGroup.a (q8Power_injective i ho he)
  · exact False.elim (q8Word_cross_ne i j hne a b he)
  · exact False.elim (q8Word_cross_ne i j hne b a he.symm)
  · exact congrArg QuaternionGroup.xa (q8Power_injective i ho (mul_left_cancel he))

theorem q8PairHom_range {G : Type*} [Group G] (i j : G)
    (ho : orderOf i = 4) (hs : j ^ 2 = i ^ 2) (hc : j * i * j⁻¹ = i⁻¹) :
    (q8PairHom i j ho hs hc).range = Subgroup.closure ({i, j} : Set G) := by
  let f := q8PairHom i j ho hs hc
  let H : Subgroup G := Subgroup.closure ({i, j} : Set G)
  have hi : i ∈ H := Subgroup.subset_closure (by simp)
  have hj : j ∈ H := Subgroup.subset_closure (by simp)
  apply le_antisymm
  · rintro g ⟨q, rfl⟩
    cases q with
    | a a => exact H.pow_mem hi a.val
    | xa a => exact H.mul_mem hj (H.pow_mem hi a.val)
  · apply (Subgroup.closure_le f.range).2
    intro g hg
    have hg' : g = i ∨ g = j := by simpa using hg
    rcases hg' with rfl | rfl
    · exact ⟨QuaternionGroup.a 1, by norm_num [f, q8PairHom, q8Word, q8Power]⟩
    · exact ⟨QuaternionGroup.xa 0, by norm_num [f, q8PairHom, q8Word, q8Power]⟩

/-- Every noncommuting pair generates a copy of the standard Q8. -/
theorem no_d8_section_contains_quaternion
    {G : Type*} [Group G] (hG : ExponentFour G)
    (hno : ¬ HasD8Section G) (i j : G) (hne : i * j ≠ j * i) :
    ∃ f : QuaternionGroup 2 →* G, Function.Injective f ∧
      f.range = Subgroup.closure ({i, j} : Set G) := by
  have hp := no_d8_section_noncommuting_pair_square_identity hG hno i j hne
  have ho : orderOf i = 4 := order_four_of_fourth_one_square_ne_one (hG i) hp.2.2.2
  have hc := no_d8_section_pair_conjugation hG hno i j hne
  exact ⟨q8PairHom i j ho hp.1.symm hc,
    q8PairHom_injective i j ho hp.1.symm hc hne,
    q8PairHom_range i j ho hp.1.symm hc⟩

end KrebsSankarQ53
