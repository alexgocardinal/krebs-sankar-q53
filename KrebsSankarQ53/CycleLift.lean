import KrebsSankarQ53.CayleyCore

/-!
# Lifting an explicit five-cycle through a group homomorphism

The five selected vertices yield a finite symmetric connection set. If their
five differences map to edges of a three-colorable Cayley graph, this set has
a three-coloring and the selected five-cycle rules out two colors.
-/

namespace KrebsSankarQ53

variable {G : Type*} [Group G]

/-- The five directed differences of a chosen closed walk. -/
def fiveCycleSteps (v₀ v₁ v₂ v₃ v₄ : G) : List G :=
  [v₀⁻¹ * v₁, v₁⁻¹ * v₂, v₂⁻¹ * v₃, v₃⁻¹ * v₄, v₄⁻¹ * v₀]

/-- The directed differences and their inverses. -/
def fiveCycleConnection (v₀ v₁ v₂ v₃ v₄ : G) : Set G :=
  {s | s ∈ fiveCycleSteps v₀ v₁ v₂ v₃ v₄ ∨
       s⁻¹ ∈ fiveCycleSteps v₀ v₁ v₂ v₃ v₄}

theorem fiveCycleConnection_inv_mem (v₀ v₁ v₂ v₃ v₄ : G) {s : G}
    (hs : s ∈ fiveCycleConnection v₀ v₁ v₂ v₃ v₄) :
    s⁻¹ ∈ fiveCycleConnection v₀ v₁ v₂ v₃ v₄ := by
  change s ∈ fiveCycleSteps v₀ v₁ v₂ v₃ v₄ ∨
    s⁻¹ ∈ fiveCycleSteps v₀ v₁ v₂ v₃ v₄ at hs
  change s⁻¹ ∈ fiveCycleSteps v₀ v₁ v₂ v₃ v₄ ∨
    (s⁻¹)⁻¹ ∈ fiveCycleSteps v₀ v₁ v₂ v₃ v₄
  rcases hs with hs | hs
  · right
    simpa using hs
  · exact Or.inl hs

/-- The connection set is drawn from a list of five steps and five inverses. -/
theorem fiveCycleConnection_finite_card_le_ten (v₀ v₁ v₂ v₃ v₄ : G) :
    (fiveCycleConnection v₀ v₁ v₂ v₃ v₄).Finite ∧
      (fiveCycleConnection v₀ v₁ v₂ v₃ v₄).ncard ≤ 10 := by
  classical
  let steps := fiveCycleSteps v₀ v₁ v₂ v₃ v₄
  let ten := steps ++ steps.map (fun s => s⁻¹)
  have hsubset : fiveCycleConnection v₀ v₁ v₂ v₃ v₄ ⊆
      (ten.toFinset : Set G) := by
    intro s hs
    change s ∈ steps ∨ s⁻¹ ∈ steps at hs
    change s ∈ ten.toFinset
    rw [List.mem_toFinset]
    apply List.mem_append.mpr
    rcases hs with hs | hs
    · exact Or.inl hs
    · right
      exact List.mem_map.mpr ⟨s⁻¹, hs, by simp⟩
  constructor
  · exact (Finset.finite_toSet _).subset hsubset
  · calc
      (fiveCycleConnection v₀ v₁ v₂ v₃ v₄).ncard ≤
          (ten.toFinset : Set G).ncard :=
        Set.ncard_le_ncard hsubset (Finset.finite_toSet _)
      _ = ten.toFinset.card := Set.ncard_coe_finset ten.toFinset
      _ ≤ ten.length := List.toFinset_card_le ten
      _ = 10 := by simp [ten, steps, fiveCycleSteps]

/-- A five-step walk whose differences are `a,b,c,b,c` needs at most five
undirected generators when `a` is an involution. -/
theorem fiveCycleConnection_finite_card_le_five_of_step_pattern
    (v₀ v₁ v₂ v₃ v₄ a b c : G)
    (ha : a * a = 1)
    (hsteps : fiveCycleSteps v₀ v₁ v₂ v₃ v₄ = [a, b, c, b, c]) :
    (fiveCycleConnection v₀ v₁ v₂ v₃ v₄).Finite ∧
      (fiveCycleConnection v₀ v₁ v₂ v₃ v₄).ncard ≤ 5 := by
  classical
  let five : List G := [a, b, b⁻¹, c, c⁻¹]
  have ha_inv : a⁻¹ = a := by
    calc
      a⁻¹ = a⁻¹ * (a * a) := by rw [ha]; simp
      _ = (a⁻¹ * a) * a := by rw [mul_assoc]
      _ = a := by simp
  have hsubset : fiveCycleConnection v₀ v₁ v₂ v₃ v₄ ⊆
      (five.toFinset : Set G) := by
    intro s hs
    change s ∈ fiveCycleSteps v₀ v₁ v₂ v₃ v₄ ∨
      s⁻¹ ∈ fiveCycleSteps v₀ v₁ v₂ v₃ v₄ at hs
    rw [hsteps] at hs
    have hcases : s = a ∨ s = b ∨ s = c ∨
        s⁻¹ = a ∨ s⁻¹ = b ∨ s⁻¹ = c := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      tauto
    change s ∈ five.toFinset
    rw [List.mem_toFinset]
    rcases hcases with h | h | h | h | h | h
    · simp [five, h]
    · simp [five, h]
    · simp [five, h]
    · have hs_a : s = a := by
        calc
          s = (s⁻¹)⁻¹ := (inv_inv s).symm
          _ = a⁻¹ := congrArg Inv.inv h
          _ = a := ha_inv
      simp [five, hs_a]
    · have hs_b : s = b⁻¹ := by
        calc
          s = (s⁻¹)⁻¹ := (inv_inv s).symm
          _ = b⁻¹ := congrArg Inv.inv h
      simp [five, hs_b]
    · have hs_c : s = c⁻¹ := by
        calc
          s = (s⁻¹)⁻¹ := (inv_inv s).symm
          _ = c⁻¹ := congrArg Inv.inv h
      simp [five, hs_c]
  constructor
  · exact (Finset.finite_toSet _).subset hsubset
  · calc
      (fiveCycleConnection v₀ v₁ v₂ v₃ v₄).ncard ≤
          (five.toFinset : Set G).ncard :=
        Set.ncard_le_ncard hsubset (Finset.finite_toSet _)
      _ = five.toFinset.card := Set.ncard_coe_finset five.toFinset
      _ ≤ five.length := List.toFinset_card_le five
      _ = 5 := by simp [five]

theorem fiveCycleConnection_edges (v₀ v₁ v₂ v₃ v₄ : G) :
    rightCayleyAdj (fiveCycleConnection v₀ v₁ v₂ v₃ v₄) v₀ v₁ ∧
    rightCayleyAdj (fiveCycleConnection v₀ v₁ v₂ v₃ v₄) v₁ v₂ ∧
    rightCayleyAdj (fiveCycleConnection v₀ v₁ v₂ v₃ v₄) v₂ v₃ ∧
    rightCayleyAdj (fiveCycleConnection v₀ v₁ v₂ v₃ v₄) v₃ v₄ ∧
    rightCayleyAdj (fiveCycleConnection v₀ v₁ v₂ v₃ v₄) v₄ v₀ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals
    unfold rightCayleyAdj fiveCycleConnection fiveCycleSteps
    first
    | refine ⟨v₀⁻¹ * v₁, ?_, by simp⟩; simp
    | refine ⟨v₁⁻¹ * v₂, ?_, by simp⟩; simp
    | refine ⟨v₂⁻¹ * v₃, ?_, by simp⟩; simp
    | refine ⟨v₃⁻¹ * v₄, ?_, by simp⟩; simp
    | refine ⟨v₄⁻¹ * v₀, ?_, by simp⟩; simp

/-- The part of section lifting that takes place inside the covering group. -/
theorem fiveCycle_lift {D : Type*} [Group D]
    (f : G →* D) (T : Set D) (c : D → Fin 3)
    (hc : CayleyProperColoring T c)
    (hT : ∀ t ∈ T, t⁻¹ ∈ T)
    (v₀ v₁ v₂ v₃ v₄ : G)
    (hsteps : ∀ s ∈ fiveCycleSteps v₀ v₁ v₂ v₃ v₄, f s ∈ T) :
    CayleyProperColoring (fiveCycleConnection v₀ v₁ v₂ v₃ v₄)
      (fun x => c (f x)) ∧
    ¬ ∃ d : G → Fin 2,
      CayleyProperColoring (fiveCycleConnection v₀ v₁ v₂ v₃ v₄) d := by
  let S := fiveCycleConnection v₀ v₁ v₂ v₃ v₄
  have hmap : ∀ s ∈ S, f s ∈ T := by
    intro s hs
    change s ∈ fiveCycleSteps v₀ v₁ v₂ v₃ v₄ ∨
      s⁻¹ ∈ fiveCycleSteps v₀ v₁ v₂ v₃ v₄ at hs
    rcases hs with hs | hs
    · exact hsteps s hs
    · have hi := hT (f s⁻¹) (hsteps s⁻¹ hs)
      simpa using hi
  constructor
  · exact cayleyColor_pullback f S T 3 hmap c hc
  · rcases fiveCycleConnection_edges v₀ v₁ v₂ v₃ v₄ with
      ⟨h₀, h₁, h₂, h₃, h₄⟩
    exact no_two_of_five_cycle S v₀ v₁ v₂ v₃ v₄ h₀ h₁ h₂ h₃ h₄

end KrebsSankarQ53
