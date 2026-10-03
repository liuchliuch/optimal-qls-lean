import OptimalQLS.TransducerCompiler.Circuit
import OptimalQLS.TransducerCompiler.Budgets

/-! # Exact circuit layouts realizing the dyadic budgets -/

noncomputable section
namespace OptimalQLS.TransducerCompiler

/-- Convert positive dividing query budgets into the two concrete schedule periods. -/
def Layout.ofBudgets {K : ℕ} (hK : 0 < K) (K₁ K₂ : ℕ)
    (h₁ : 0 < K₁) (h₂ : 0 < K₂) (hdiv₁ : K₁ ∣ K) (hdiv₂ : K₂ ∣ K) : Layout K where
  positive := hK
  D₁ := K / K₁
  D₂ := K / K₂
  positive₁ := Nat.div_pos (Nat.le_of_dvd hK hdiv₁) h₁
  positive₂ := Nat.div_pos (Nat.le_of_dvd hK hdiv₂) h₂
  le₁ := Nat.div_le_self K K₁
  le₂ := Nat.div_le_self K K₂
  divides₁ := Nat.div_dvd_of_dvd hdiv₁
  divides₂ := Nat.div_dvd_of_dvd hdiv₂

/-- The generated instruction list realizes precisely the three requested budgets. -/
theorem Layout.ofBudgets_exact_counts {K : ℕ} (hK : 0 < K) (K₁ K₂ : ℕ)
    (h₁ : 0 < K₁) (h₂ : 0 < K₂) (hdiv₁ : K₁ ∣ K) (hdiv₂ : K₂ ∣ K) :
    let b := Layout.ofBudgets hK K₁ K₂ h₁ h₂ hdiv₁ hdiv₂
    (compile b).workCalls = K ∧
    (compile b).firstCalls = K₁ ∧
    (compile b).secondCalls = K₂ := by
  dsimp only
  refine ⟨prefix_workCalls _ K, ?_, ?_⟩
  · rw [compile, prefix_firstCalls]
    exact scheduledCount_quotient hK h₁ hdiv₁
  · rw [compile, prefix_secondCalls]
    exact scheduledCount_quotient hK h₂ hdiv₂

namespace BudgetParameters

variable {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ)

/-- The concrete layout used with the Appendix A.2 parameter choice. -/
def layout : Layout (mainBudget κ) :=
  Layout.ofBudgets (mainBudget_pos κ) (mainBudget κ) (reflectionBudget κ ŝ)
    (mainBudget_pos κ) (reflectionBudget_pos κ ŝ) dvd_rfl h.reflectionBudget_dvd_mainBudget

@[simp] theorem layout_D₁ : h.layout.D₁ = 1 := by
  change mainBudget κ / mainBudget κ = 1
  exact Nat.div_self (mainBudget_pos κ)

@[simp] theorem layout_D₂ : h.layout.D₂ = mainBudget κ / reflectionBudget κ ŝ := rfl

/-- Exact work, first-oracle, and second-oracle counts for the manuscript's budgets. -/
theorem layout_exact_counts :
    (compile h.layout).workCalls = mainBudget κ ∧
    (compile h.layout).firstCalls = mainBudget κ ∧
    (compile h.layout).secondCalls = reflectionBudget κ ŝ :=
  Layout.ofBudgets_exact_counts (mainBudget_pos κ) (mainBudget κ) (reflectionBudget κ ŝ)
    (mainBudget_pos κ) (reflectionBudget_pos κ ŝ) dvd_rfl h.reflectionBudget_dvd_mainBudget

end BudgetParameters
end OptimalQLS.TransducerCompiler
