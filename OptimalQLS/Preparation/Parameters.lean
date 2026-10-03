import OptimalQLS.Preparation.OriginalQueries

/-! # Code selection from classical input parameters alone -/
noncomputable section
namespace OptimalQLS.Preparation
open TransducerCompiler

def knownScaleWitness (κ ŝ : ℝ) : ℝ := min κ (max 1 (2*ŝ/5))

/-- This witness depends only on the supplied classical parameters. It is used
to construct the circuit; the hidden true solution norm is used only later in
its proof of correctness and resource bounds. -/
theorem knownScaleWitness_budget {κ ŝ : ℝ} (hκ : 2≤κ)
    (hlo : 3/8≤ŝ) (hhi : ŝ≤5*κ/2) : BudgetParameters κ (knownScaleWitness κ ŝ) ŝ := by
  have hspos : 0<ŝ := by linarith
  refine ⟨hκ,?_,?_,?_,?_⟩
  · exact le_min (by linarith) (le_max_left _ _)
  · exact min_le_left _ _
  · have hm : max 1 (2*ŝ/5)≤8*ŝ/3 := max_le (by linarith) (by nlinarith)
    have h := (min_le_right κ (max 1 (2*ŝ/5))).trans hm
    change 3*min κ (max 1 (2*ŝ/5))/8≤ŝ
    linarith
  · have hm : 2*ŝ/5≤min κ (max 1 (2*ŝ/5)) := le_min (by linarith) (le_max_right _ _)
    change ŝ≤5*min κ (max 1 (2*ŝ/5))/2
    linarith

theorem classical_parameter_range {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ) :
    3/8≤ŝ ∧ ŝ≤5*κ/2 := by
  constructor <;> nlinarith [h.scale_ge_one,h.scale_le_kappa,h.estimate_lower,h.estimate_upper]

variable {S D : Type*} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]

def selectedPreparationCircuit (s₀ : S) (i₀ : D) {κ ŝ : ℝ}
    (hκ : 2≤κ) (hlo : 3/8≤ŝ) (hhi : ŝ≤5*κ/2) :=
  originalPreparationAlgorithm s₀ i₀ (knownScaleWitness_budget hκ hlo hhi)

theorem selectedPreparationCircuit_eq (s₀ : S) (i₀ : D) {κ s ŝ : ℝ}
    (h : BudgetParameters κ s ŝ) :
    selectedPreparationCircuit s₀ i₀ h.kappa_ge_two (classical_parameter_range h).1 (classical_parameter_range h).2=
      originalPreparationAlgorithm s₀ i₀ h := originalPreparationAlgorithm_uniform_in_scale _ _ _ _

end OptimalQLS.Preparation
