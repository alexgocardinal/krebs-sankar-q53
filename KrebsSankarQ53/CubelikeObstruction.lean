import KrebsSankarQ53.CubelikeWinding
import KrebsSankarQ53.SubgroupLift

/-!
# The cubelike obstruction, including infinite groups

Reversing an exponent-two walk leaves its multiset of steps unchanged.
Permutation invariance of the winding sum therefore identifies the
winding sum with its negative. Every closed walk has even length.
Path parity colors the generated subgroup with two colors, and the
existing coset extension colors every component of the Cayley graph.
No finiteness assumption is imposed on the group or connection set.
-/

namespace KrebsSankarQ53
namespace CubelikeWinding

variable {G : Type*} [AddCommGroup G]

theorem neg_eq_self_of_add_self_zero (hG : ∀ g : G, g + g = 0) (g : G) : -g = g := by
  calc
    -g = -g + (g + g) := by rw [hG]; simp
    _ = g := by abel

theorem W_reverse_exponent_two (hG : ∀ g : G, g + g = 0)
    {S : Set G} {c : G → ZMod 3}
    (hc : ∀ g, ∀ s ∈ S, c (g + s) ≠ c g) :
    ∀ (L : List G), (∀ s ∈ L, s ∈ S) → ∀ g,
      W c (g + L.sum) L.reverse = -W c g L := by
  intro L
  induction L with
  | nil => intro _ g; simp
  | cons s L ih =>
    intro hL g
    have hs : s ∈ S := hL s (by simp)
    have hmem : ∀ t ∈ L, t ∈ S := fun t ht => hL t (List.mem_cons_of_mem s ht)
    have hend : (g + s + L.sum) + L.reverse.sum = g + s := by
      rw [List.sum_reverse]
      calc
        (g + s + L.sum) + L.sum = (g + s) + (L.sum + L.sum) := by abel
        _ = g + s := by rw [hG, add_zero]
    have hsig : sig c (g + s) s = -sig c g s := by
      simpa only [neg_eq_self_of_add_self_zero hG s] using sig_neg hc hs g
    rw [List.sum_cons, ← add_assoc, List.reverse_cons, W_append,
      ih hmem (g + s), hend]
    simp only [W_cons, W_nil, add_zero, hsig]
    ring

theorem exponent_two_closed_walk_even (hG : ∀ g : G, g + g = 0)
    {S : Set G} {c : G → ZMod 3}
    (hc : ∀ g, ∀ s ∈ S, c (g + s) ≠ c g)
    (L : List G) (hL : ∀ s ∈ L, s ∈ S) (h0 : L.sum = 0) :
    L.length % 2 = 0 := by
  have hrev := W_reverse_exponent_two hG hc L hL 0
  have hperm := W_perm hc L.reverse_perm 0 (by simpa using hL)
  rw [h0, add_zero] at hrev
  have hzero : W c 0 L = 0 := by omega
  have hpar := W_parity c L 0
  rw [hzero] at hpar
  omega

theorem exponent_two_closure_two_coloring (hG : ∀ g : G, g + g = 0)
    (S : Set G) (c : G → ZMod 3)
    (hc : ∀ g, ∀ s ∈ S, c (g + s) ≠ c g) :
    ∃ b : AddSubgroup.closure S → Fin 2,
      ∀ (g : AddSubgroup.closure S) (s : G) (hs : s ∈ S),
        b ⟨(g : G) + s, (AddSubgroup.closure S).add_mem g.property
          (AddSubgroup.subset_closure hs)⟩ ≠ b g := by
  classical
  have hS : ∀ s ∈ S, -s ∈ S := by
    intro s hs
    simpa only [neg_eq_self_of_add_self_zero hG s] using hs
  have hlist (g : AddSubgroup.closure S) :
      ∃ L : List G, (∀ s ∈ L, s ∈ S) ∧ L.sum = (g : G) :=
    exists_list_of_mem_closure hS g.property
  choose path hpath hsum using hlist
  let b : AddSubgroup.closure S → Fin 2 :=
    fun g => ⟨(path g).length % 2, Nat.mod_lt _ (by decide)⟩
  refine ⟨b, ?_⟩
  intro g s hs he
  let y : AddSubgroup.closure S :=
    ⟨(g : G) + s, (AddSubgroup.closure S).add_mem g.property
      (AddSubgroup.subset_closure hs)⟩
  have hmem : ∀ t ∈ path g ++ [s] ++ path y, t ∈ S := by
    intro t ht
    simp only [List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | ht | ht
    · exact hpath g t ht
    · simpa only [ht] using hs
    · exact hpath y t ht
  have hzero : (path g ++ [s] ++ path y).sum = 0 := by
    simp only [List.sum_append, List.sum_singleton, hsum]
    simpa only [add_assoc] using hG ((g : G) + s)
  have heven := exponent_two_closed_walk_even hG hc _ hmem hzero
  have hvals : (path y).length % 2 = (path g).length % 2 := congrArg Fin.val he
  simp only [List.length_append, List.length_singleton] at heven
  omega

end CubelikeWinding

/-- Cubelike Cayley graphs cannot have chromatic number exactly three.
This formulation includes arbitrary infinite elementary abelian groups
and arbitrary connection sets. -/
theorem elementaryAbelian_cayley_three_implies_two
    {G : Type*} [CommGroup G] (hG : ∀ g : G, g * g = 1)
    (S : Set G) (c : G → Fin 3) (hc : CayleyProperColoring S c) :
    ∃ b : G → Fin 2, CayleyProperColoring S b := by
  classical
  let A := Additive G
  let T : Set A := {a | Additive.toMul a ∈ S}
  let ca : A → ZMod 3 := fun a => ((c (Additive.toMul a)).val : ZMod 3)
  have hcast : Function.Injective (fun a : Fin 3 => (a.val : ZMod 3)) := by
    intro a b he
    apply Fin.ext
    have hv := congrArg ZMod.val he
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt,
      Nat.mod_eq_of_lt b.isLt] using hv
  have hA : ∀ a : A, a + a = 0 := hG
  have hca : ∀ a : A, ∀ t ∈ T, ca (a + t) ≠ ca a := by
    intro a t ht he
    apply hc (Additive.toMul a) (Additive.toMul (a + t))
      ⟨Additive.toMul t, ht, rfl⟩
    exact (hcast he).symm
  obtain ⟨b, hb⟩ := CubelikeWinding.exponent_two_closure_two_coloring hA T ca hca
  let H := AddSubgroup.closure T
  let K : Subgroup G :=
    { carrier := {g | Additive.ofMul g ∈ H}
      one_mem' := H.zero_mem
      mul_mem' := fun ha hb => H.add_mem ha hb
      inv_mem' := fun ha => H.neg_mem ha }
  let U : Set K := {s | (s : G) ∈ S}
  let bk : K → Fin 2 := fun g => b ⟨Additive.ofMul (g : G), g.property⟩
  have hbk : CayleyProperColoring U bk := by
    intro x y hxy
    rcases hxy with ⟨s, hs, rfl⟩
    exact (hb ⟨Additive.ofMul (x : G), x.property⟩
      (Additive.ofMul (s : G)) hs).symm
  have hconn : subgroupConnection K U = S := by
    ext g
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · intro hg
      have hk : g ∈ K := AddSubgroup.subset_closure hg
      exact ⟨⟨g, hk⟩, hg, rfl⟩
  obtain ⟨C, hC⟩ := subgroup_color_extend K U 2 bk hbk
  exact ⟨C, by simpa only [hconn] using hC⟩

end KrebsSankarQ53
