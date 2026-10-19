import KrebsSankarQ53.D8WordSurjective
import KrebsSankarQ53.DihedralGenerated

/-!
# Identifying the generated subgroup with D8

When the two involutions do not commute, their generated subgroup and the
concrete D8 group both have eight elements. The surjective word homomorphism
is therefore an isomorphism.
-/

namespace KrebsSankarQ53

theorem d8WordHom_bijective {G : Type*} [Group G]
    (hG : ExponentFour G) {a b : G}
    (ha : a * a = 1) (hb : b * b = 1)
    (hne : a * b ≠ b * a) :
    Function.Bijective (d8WordHom hG ha hb) := by
  letI : Finite D8 := Finite.of_equiv (Fin 8) d8EquivFin.symm
  have hcard : Nat.card D8 ≤
      Nat.card (Subgroup.closure ({a, b} : Set G)) := by
    simpa only [d8_nat_card,
      noncommuting_involutions_closure_card_eight hG ha hb hne]
      using (le_refl (8 : ℕ))
  exact (d8WordHom_surjective hG ha hb).bijective_of_nat_card_le hcard

/-- An isomorphism from the concrete D8 group to the subgroup generated
by noncommuting involutions in an exponent-four group. -/
noncomputable def d8GeneratedEquiv {G : Type*} [Group G]
    (hG : ExponentFour G) {a b : G}
    (ha : a * a = 1) (hb : b * b = 1)
    (hne : a * b ≠ b * a) :
    D8 ≃* Subgroup.closure ({a, b} : Set G) :=
  MulEquiv.ofBijective (d8WordHom hG ha hb)
    (d8WordHom_bijective hG ha hb hne)

/-- The inverse is a surjective homomorphism from the generated subgroup
to the concrete D8 group. -/
noncomputable def d8GeneratedSection {G : Type*} [Group G]
    (hG : ExponentFour G) {a b : G}
    (ha : a * a = 1) (hb : b * b = 1)
    (hne : a * b ≠ b * a) :
    Subgroup.closure ({a, b} : Set G) →* D8 :=
  (d8GeneratedEquiv hG ha hb hne).symm.toMonoidHom

theorem d8GeneratedSection_surjective {G : Type*} [Group G]
    (hG : ExponentFour G) {a b : G}
    (ha : a * a = 1) (hb : b * b = 1)
    (hne : a * b ≠ b * a) :
    Function.Surjective (d8GeneratedSection hG ha hb hne) :=
  (d8GeneratedEquiv hG ha hb hne).symm.surjective

end KrebsSankarQ53
