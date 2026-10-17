import Mathlib

/-!
# First Lean checkpoint: the eight-vertex dihedral Cayley graph

Vertex `a + 4*b` represents `r^a s^b`, where `0 ≤ a < 4` and `0 ≤ b < 2`.
The connection set is `{r^2, s, rs}` = `{2, 4, 5}`.

This file concerns only the finite witness.  It does not prove the group
classification, section lifting, or the quaternionic obstruction.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 5000000

namespace KrebsSankarQ53

/-- Multiplication on the concrete encoding of the dihedral group of order 8. -/
def dmul (x y : Fin 8) : Fin 8 :=
  let a := x.val % 4
  let b := x.val / 4
  let c := y.val % 4
  let d := y.val / 4
  Fin.ofNat 8 ((a + (if b = 0 then c else (4 - c) % 4)) % 4 + 4 * ((b + d) % 2))

/-- The three generators `r^2`, `s`, and `rs`. -/
def generators : List (Fin 8) := [2, 4, 5]

/-- Right Cayley adjacency in the eight-element model. -/
def cayAdj (u v : Fin 8) : Prop :=
  ∃ s : Fin 8, s ∈ generators ∧ v = dmul u s

/-- An explicit, independently inspectable edge list for the same graph. -/
def edges : List (Fin 8 × Fin 8) :=
  [(0, 2), (0, 4), (0, 5),
   (1, 3), (1, 5), (1, 6),
   (2, 6), (2, 7),
   (3, 4), (3, 7),
   (4, 6), (5, 7)]

def adj (u v : Fin 8) : Prop :=
  (u, v) ∈ edges ∨ (v, u) ∈ edges

-- Give Lean executable decision procedures for the two adjacency relations.
instance (u v : Fin 8) : Decidable (cayAdj u v) := by
  unfold cayAdj
  infer_instance

instance (u v : Fin 8) : Decidable (adj u v) := by
  unfold adj
  infer_instance

/-- The proposed multiplication really is associative. -/
theorem dmul_assoc : ∀ x y z : Fin 8,
    dmul (dmul x y) z = dmul x (dmul y z) := by
  decide

theorem dmul_one_left : ∀ x : Fin 8, dmul 0 x = x := by
  decide

theorem dmul_one_right : ∀ x : Fin 8, dmul x 0 = x := by
  decide

theorem dmul_inverses : ∀ x : Fin 8,
    ∃ y : Fin 8, dmul x y = 0 ∧ dmul y x = 0 := by
  decide

theorem generators_are_involutions : ∀ s : Fin 8,
    s ∈ generators → dmul s s = 0 := by
  decide

theorem adj_iff_cayAdj : ∀ u v : Fin 8, adj u v ↔ cayAdj u v := by
  decide

theorem cayAdj_symmetric : ∀ u v : Fin 8,
    cayAdj u v ↔ cayAdj v u := by
  decide

theorem cayAdj_irreflexive : ∀ u : Fin 8, ¬ cayAdj u u := by
  decide

/-- The tuple `(0,0,1,2,1,1,2,0)` from the manuscript. -/
def threeColor (v : Fin 8) : Fin 3 :=
  match v.val with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 1
  | 5 => 1
  | 6 => 2
  | _ => 0

def ProperColoring (n : Nat) (c : Fin 8 → Fin n) : Prop :=
  ∀ u v : Fin 8, adj u v → c u ≠ c v

instance (n : Nat) (c : Fin 8 → Fin n) : Decidable (ProperColoring n c) := by
  unfold ProperColoring
  infer_instance

theorem threeColor_proper : ProperColoring 3 threeColor := by
  decide

/-- The displayed cycle is `1,r²,r²s,r,rs,1`. -/
theorem fiveCycle :
    adj 0 2 ∧ adj 2 6 ∧ adj 6 1 ∧ adj 1 5 ∧ adj 5 0 := by
  decide

/-- Five successive changes of two colors cannot close into a cycle. -/
private theorem five_not_two :
    ¬ ∃ a b c d e : Fin 2,
      a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ e ∧ e ≠ a := by
  decide

theorem no_two_coloring : ¬ ∃ c : Fin 8 → Fin 2, ProperColoring 2 c := by
  rintro ⟨c, hc⟩
  have h02 : c 0 ≠ c 2 := hc 0 2 (by decide)
  have h26 : c 2 ≠ c 6 := hc 2 6 (by decide)
  have h61 : c 6 ≠ c 1 := hc 6 1 (by decide)
  have h15 : c 1 ≠ c 5 := hc 1 5 (by decide)
  have h50 : c 5 ≠ c 0 := hc 5 0 (by decide)
  exact five_not_two ⟨c 0, c 2, c 6, c 1, c 5,
    h02, h26, h61, h15, h50⟩

/-- An exact three-chromatic coloring statement for the concrete Cayley graph. -/
theorem concrete_cayley_witness :
    (∃ c : Fin 8 → Fin 3,
      ∀ u v : Fin 8, cayAdj u v → c u ≠ c v) ∧
    ¬ (∃ c : Fin 8 → Fin 2,
      ∀ u v : Fin 8, cayAdj u v → c u ≠ c v) := by
  constructor
  · refine ⟨threeColor, ?_⟩
    intro u v huv
    exact threeColor_proper u v ((adj_iff_cayAdj u v).mpr huv)
  · rintro ⟨c, hc⟩
    apply no_two_coloring
    refine ⟨c, ?_⟩
    intro u v huv
    exact hc u v ((adj_iff_cayAdj u v).mp huv)

end KrebsSankarQ53
