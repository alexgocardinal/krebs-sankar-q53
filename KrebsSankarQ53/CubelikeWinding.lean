import KrebsSankarQ53.CayleyCore

/-
Adapted from Sergi Galán, lean/TheoremW.lean, at commit
cb660f322dce47a773f347d39818ffc46e6ca72c of decalion89/chromatic-number-of-the-plane.
Only the combinatorial winding and generator-list lemmas are retained;
the original Lean 4.34.1 imports are replaced by the project's Mathlib import.
MIT License

Copyright (c) 2026 Sergi Galán

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

-/

/-!
# Combinatorial winding sums
These lemmas use no finiteness hypothesis and no real-valued averaging.
-/

set_option autoImplicit false

namespace KrebsSankarQ53.CubelikeWinding

/-- `sgn3 a b ∈ {1, -1}` is the integer lift of `b - a` (when `a ≠ b`). -/
def sgn3 (a b : ZMod 3) : ℤ := if b - a = 1 then 1 else -1

lemma sgn3_eq_one_or (a b : ZMod 3) : sgn3 a b = 1 ∨ sgn3 a b = -1 := by
  unfold sgn3; split_ifs <;> simp

lemma zmod3_cases : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = -1 := by decide

lemma sgn3_cast {a b : ZMod 3} (h : b ≠ a) : ((sgn3 a b : ℤ) : ZMod 3) = b - a := by
  unfold sgn3
  split_ifs with h1
  · rw [h1, Int.cast_one]
  · rcases zmod3_cases (b - a) with h2 | h2 | h2
    · exact absurd (sub_eq_zero.1 h2) h
    · exact absurd h2 h1
    · rw [h2, Int.cast_neg, Int.cast_one]

lemma three_dvd_of_cast {x : ℤ} (h : ((x : ℤ) : ZMod 3) = 0) : (3 : ℤ) ∣ x := by
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd x 3).1 h
  exact_mod_cast this

lemma sgn3_antisymm {a b : ZMod 3} (h : b ≠ a) : sgn3 b a = - sgn3 a b := by
  have h3 : (3 : ℤ) ∣ sgn3 b a + sgn3 a b := three_dvd_of_cast (by
    push_cast
    rw [sgn3_cast h, sgn3_cast h.symm]
    ring)
  rcases sgn3_eq_one_or a b with h4 | h4 <;> rcases sgn3_eq_one_or b a with h5 | h5 <;> omega

/-- Squares do not wind: both sides lie in `{-2, 0, 2}` and agree mod `3`. -/
lemma sgn3_square {a b c d : ZMod 3} (hab : b ≠ a) (hbd : d ≠ b) (hac : c ≠ a) (hcd : d ≠ c) :
    sgn3 a b + sgn3 b d = sgn3 a c + sgn3 c d := by
  have h3 : (3 : ℤ) ∣ sgn3 a b + sgn3 b d - sgn3 a c - sgn3 c d := three_dvd_of_cast (by
    push_cast
    rw [sgn3_cast hab, sgn3_cast hbd, sgn3_cast hac, sgn3_cast hcd]
    ring)
  rcases sgn3_eq_one_or a b with h1 | h1 <;> rcases sgn3_eq_one_or b d with h2 | h2 <;>
    rcases sgn3_eq_one_or a c with h4 | h4 <;> rcases sgn3_eq_one_or c d with h5 | h5 <;> omega

/-! ### Winding sums of walks -/

variable {G : Type*} [AddCommGroup G]

/-- `sig c g s = σ(g, s) ∈ {±1}`, the integer lift of `c (g + s) - c g`. -/
def sig (c : G → ZMod 3) (g s : G) : ℤ := sgn3 (c g) (c (g + s))

lemma sig_eq_one_or (c : G → ZMod 3) (g s : G) : sig c g s = 1 ∨ sig c g s = -1 :=
  sgn3_eq_one_or _ _

/-- `σ(g + s, -s) = -σ(g, s)`. -/
lemma sig_neg {S : Set G} {c : G → ZMod 3} (hc : ∀ g, ∀ s ∈ S, c (g + s) ≠ c g)
    {s : G} (hs : s ∈ S) (g : G) : sig c (g + s) (-s) = - sig c g s := by
  unfold sig
  rw [add_neg_cancel_right]
  exact sgn3_antisymm (hc g s hs)

/-- The winding sum `W(g, L) = ∑_j σ(g + s₁ + ⋯ + s_{j-1}, s_j)` of the walk from `g` with
steps `L = [s₁, …, s_N]`. -/
def W (c : G → ZMod 3) : G → List G → ℤ
  | _, [] => 0
  | g, s :: L => sig c g s + W c (g + s) L

@[simp] lemma W_nil (c : G → ZMod 3) (g : G) : W c g [] = 0 := rfl

@[simp] lemma W_cons (c : G → ZMod 3) (g s : G) (L : List G) :
    W c g (s :: L) = sig c g s + W c (g + s) L := rfl

lemma W_append (c : G → ZMod 3) (g : G) (L₁ L₂ : List G) :
    W c g (L₁ ++ L₂) = W c g L₁ + W c (g + L₁.sum) L₂ := by
  induction L₁ generalizing g with
  | nil => simp
  | cons x L ih => simp [ih, add_assoc]

/-- The winding sum is invariant under permutations of the steps (squares do not wind). -/
lemma W_perm {S : Set G} {c : G → ZMod 3} (hc : ∀ g, ∀ s ∈ S, c (g + s) ≠ c g)
    {L L' : List G} (hp : L.Perm L') : ∀ g, (∀ x ∈ L, x ∈ S) → W c g L = W c g L' := by
  induction hp with
  | nil => intro g _; rfl
  | cons x _ ih =>
    intro g hL
    simp only [W_cons]
    rw [ih (g + x) (fun y hy => hL y (List.mem_cons_of_mem x hy))]
  | swap x y l =>
    intro g hL
    have hx : x ∈ S := hL x (by simp)
    have hy : y ∈ S := hL y (by simp)
    have hyx : g + y + x = g + x + y := add_right_comm g y x
    have hbd : c (g + x + y) ≠ c (g + y) := by rw [← hyx]; exact hc (g + y) x hx
    have h := sgn3_square (hc g y hy) hbd (hc g x hx) (hc (g + x) y hy)
    simp only [W_cons, sig, hyx]
    omega
  | trans h₁ _ ih₁ ih₂ =>
    intro g hL
    rw [ih₁ g hL, ih₂ g (fun y hy => hL y (h₁.symm.subset hy))]

/-- Telescoping in `ZMod 3`. -/
lemma W_cast {S : Set G} {c : G → ZMod 3} (hc : ∀ g, ∀ s ∈ S, c (g + s) ≠ c g) :
    ∀ (L : List G) (g : G), (∀ x ∈ L, x ∈ S) →
      ((W c g L : ℤ) : ZMod 3) = c (g + L.sum) - c g
  | [], g, _ => by simp
  | s :: L, g, hL => by
    have hs : s ∈ S := hL s (by simp)
    have ih := W_cast hc L (g + s) (fun x hx => hL x (List.mem_cons_of_mem s hx))
    rw [W_cons, Int.cast_add, ih, sig, sgn3_cast (hc g s hs), List.sum_cons,
      show g + (s + L.sum) = g + s + L.sum from (add_assoc _ _ _).symm]
    ring

lemma W_parity (c : G → ZMod 3) : ∀ (L : List G) (g : G), W c g L % 2 = (L.length : ℤ) % 2
  | [], g => by simp
  | s :: L, g => by
    have ih := W_parity c L (g + s)
    rw [W_cons, List.length_cons]
    push_cast
    rcases sig_eq_one_or c g s with h | h <;> omega

/-- A closed walk has winding sum `3 w` with `w ≡ N (mod 2)`. -/
lemma W_closed {S : Set G} {c : G → ZMod 3} (hc : ∀ g, ∀ s ∈ S, c (g + s) ≠ c g)
    {L : List G} (hL : ∀ x ∈ L, x ∈ S) (h0 : L.sum = 0) (g : G) :
    ∃ m : ℤ, W c g L = 3 * (2 * m - L.length) := by
  have h3 : (3 : ℤ) ∣ W c g L := by
    apply three_dvd_of_cast
    rw [W_cast hc L g hL, h0, add_zero, sub_self]
  have h2 := W_parity c L g
  exact ⟨(W c g L / 3 + L.length) / 2, by omega⟩

/-- Moving the base point of a closed walk by `s ∈ S` does not change the winding sum. -/
lemma W_shift {S : Set G} (hS : ∀ s ∈ S, -s ∈ S) {c : G → ZMod 3}
    (hc : ∀ g, ∀ s ∈ S, c (g + s) ≠ c g) {L : List G} (hL : ∀ x ∈ L, x ∈ S)
    (h0 : L.sum = 0) {s : G} (hs : s ∈ S) (g : G) : W c (g + s) L = W c g L := by
  have hmem : ∀ x ∈ L ++ [s, -s], x ∈ S := by
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hL x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hs
      · exact hS s hs
  have h := W_perm hc (List.perm_middle (l₁ := L) (a := s) (l₂ := [-s])) g hmem
  simp only [W_append, W_cons, W_nil, h0, add_zero, sig_neg hc hs] at h
  linarith

/-- The winding sum of a closed walk only depends on the coset of the base point. -/
lemma W_shift_closure {S : Set G} (hS : ∀ s ∈ S, -s ∈ S) {c : G → ZMod 3}
    (hc : ∀ g, ∀ s ∈ S, c (g + s) ≠ c g) {L : List G} (hL : ∀ x ∈ L, x ∈ S)
    (h0 : L.sum = 0) {γ : G} (hγ : γ ∈ AddSubgroup.closure S) :
    ∀ g, W c (g + γ) L = W c g L := by
  induction hγ using AddSubgroup.closure_induction with
  | mem x hx => exact W_shift hS hc hL h0 hx
  | zero => intro g; rw [add_zero]
  | add x y _ _ ihx ihy => intro g; rw [← add_assoc, ihy, ihx]
  | neg x _ ih => intro g; rw [← ih (g + -x), neg_add_cancel_right]

/-! ### Lists of generators -/

lemma list_sum_map_neg (L : List G) : (L.map (fun z => -z)).sum = -L.sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.sum_cons, ih, neg_add]

/-- Every element of the closure of a symmetric set `S` is the sum of a list of elements
of `S`. -/
lemma exists_list_of_mem_closure {S : Set G} (hS : ∀ s ∈ S, -s ∈ S) {γ : G}
    (hγ : γ ∈ AddSubgroup.closure S) : ∃ L : List G, (∀ x ∈ L, x ∈ S) ∧ L.sum = γ := by
  induction hγ using AddSubgroup.closure_induction with
  | mem x hx => exact ⟨[x], by simpa using hx, by simp⟩
  | zero => exact ⟨[], by simp, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨L₁, h₁, e₁⟩ := ihx
    obtain ⟨L₂, h₂, e₂⟩ := ihy
    exact ⟨L₁ ++ L₂, fun z hz => (List.mem_append.1 hz).elim (h₁ z) (h₂ z), by
      rw [List.sum_append, e₁, e₂]⟩
  | neg x _ ih =>
    obtain ⟨L, h, e⟩ := ih
    refine ⟨L.map (fun z => -z), fun z hz => ?_, by rw [list_sum_map_neg, e]⟩
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
    exact hS y (h y hy)


end KrebsSankarQ53.CubelikeWinding
