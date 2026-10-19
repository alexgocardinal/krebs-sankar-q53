import KrebsSankarQ53.D8WordEquiv
import KrebsSankarQ53.D8FiveLift

/-!
# The obstruction from noncommuting involutions

Two noncommuting involutions in an exponent-four group generate a D8
subgroup. The established D8-section theorem then produces a Cayley graph
with chromatic number exactly three and a connection set of size at most five.
-/

namespace KrebsSankarQ53

/-- Noncommuting involutions provide a five-generator obstruction to the
property that all three-colorable Cayley graphs are bipartite. -/
theorem noncommuting_involutions_three_chromatic_cayley_five
    {G : Type*} [Group G] (hG : ExponentFour G)
    {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hne : a * b ≠ b * a) :
    ∃ S : Set G, S.Finite ∧ S.ncard ≤ 5 ∧
      (∃ c : G → Fin 3, CayleyProperColoring S c) ∧
      ¬ ∃ c : G → Fin 2, CayleyProperColoring S c := by
  let H : Subgroup G := Subgroup.closure ({a, b} : Set G)
  let f : H →* D8 := d8GeneratedSection hG ha hb hne
  exact d8_section_has_three_chromatic_cayley_five hG H f
    (d8GeneratedSection_surjective hG ha hb hne)

end KrebsSankarQ53
