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
