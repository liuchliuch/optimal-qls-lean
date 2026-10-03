import OptimalQLS.Preparation.Parameters
import OptimalQLS.PolynomialTransform.ParameterBounds

/-! # Explicit one-run and repetition resource constants -/
noncomputable section
namespace OptimalQLS.Refinement
open TransducerCompiler Preparation

theorem log_accuracy_lower {ε : ℝ} (hε0 : 0<ε) (hε1 : ε<1/2) :
    (1/2 : ℝ)≤Real.log (1/ε) := by
  have h := PolynomialTransform.kappa_log_ge_one (κ := 2) (by norm_num) hε0 hε1
  linarith

theorem log_refinement_accuracy {ε : ℝ} (hε0 : 0<ε) (hε1 : ε<1/2) :
    Real.log (1/(ε/1024))≤11*Real.log (1/ε) := by
  have he : (1 : ℝ)/(ε/1024)=2^10*(1/ε) := by ring
  have ht : (2 : ℝ)≤1/ε := (le_div_iff₀ hε0).mpr (by linarith)
  have hl := Real.log_le_log (by norm_num : (0 : ℝ)<2) ht
  rw [he,Real.log_mul (by positivity) (by positivity),Real.log_pow]
  norm_num at hl ⊢
  linarith

theorem one_run_matrix_bound {κ s ŝ ε : ℝ} (h : BudgetParameters κ s ŝ)
    (hε0 : 0<ε) (hε1 : ε<1/2) :
    2*(mainBudget κ : ℝ)+840096*κ*Real.log (1/(ε/1024)) <
      1100000000*κ*Real.log (1/ε) := by
  have hm := h.mainBudget_bounds.2
  have hl := log_accuracy_lower hε0 hε1
  have he := log_refinement_accuracy hε0 hε1
  have hk := h.kappa_pos
  have he' := mul_le_mul_of_nonneg_left he (show 0≤840096*κ by positivity)
  have hl' := mul_le_mul_of_nonneg_left hl (show 0≤1024000000*κ by positivity)
  nlinarith

theorem one_run_vector_bound {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ) :
    ((2*reflectionBudget κ ŝ+1 : ℕ) : ℝ)<120000001*(κ/s) := by
  have hs : 0<s := by linarith [h.scale_ge_one]
  have hk : 1≤κ/s := (le_div_iff₀ hs).mpr (by simpa using h.scale_le_kappa)
  have hb := h.reflectionBudget_scale_bound
  push_cast
  linarith

theorem repetition_query_bounds {κ s ŝ ε : ℝ} (h : BudgetParameters κ s ŝ)
    (hε0 : 0<ε) (hε1 : ε<1/2) (qa qb : ℕ)
    (ha : (qa : ℝ)<2*mainBudget κ+840096*κ*Real.log (1/(ε/1024)))
    (hb : qb=2*reflectionBudget κ ŝ+1) :
    ((72000*qa : ℕ) : ℝ)<79200000000000*κ*Real.log (1/ε) ∧
      ((72000*qb : ℕ) : ℝ)<8640000072000*(κ/s) := by
  have ham := lt_trans ha (one_run_matrix_bound h hε0 hε1)
  have hbm := one_run_vector_bound h
  rw [←hb] at hbm
  push_cast
  constructor <;> nlinarith

end OptimalQLS.Refinement
