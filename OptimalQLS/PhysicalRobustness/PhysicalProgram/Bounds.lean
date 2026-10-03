import OptimalQLS.PhysicalRobustness.PhysicalProgram.Execution

/-! Uniform logarithmic bounds on the actual run and its repeated query depths. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1000000
open scoped Classical Matrix.Norms.L2Operator
namespace OptimalQLS.PhysicalRobustness.PhysicalProgram
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform PhysicalPadding Refinement
open Refinement.PhysicalProgram
variable {a n : ℕ} {κ ŝ ε : ℝ}

/-- The refinement precision is ε/4096=ε/2^12. -/
theorem log_noisy_accuracy (hε : 0<ε) (hε1 : ε<1/2) :
    Real.log (1/(ε/4096))≤13*Real.log (1/ε) := by
  have he : (1 : ℝ)/(ε/4096)=2^12*(1/ε) := by ring
  have ht : (2 : ℝ)≤1/ε := (le_div_iff₀ hε).mpr (by linarith)
  have hl := Real.log_le_log (by norm_num : (0 : ℝ)<2) ht
  rw [he,Real.log_mul (by positivity) (by positivity),Real.log_pow]
  norm_num at hl ⊢
  linarith

theorem Implementation.matrix_bound_log (I : Implementation a n κ ŝ ε)
    (hε : 0<ε) (hε1 : ε<1/2) :
    (I.runCircuit.matrixQueries : ℝ)<445000000000*κ*Real.log (1/ε) := by
  have he := log_noisy_accuracy hε hε1
  have hl := log_accuracy_lower hε hε1
  have hk : 0<κ := by linarith [I.kappa_ge_two]
  have hm := mul_le_mul_of_nonneg_left he (show 0≤34004000192*κ by positivity)
  have hn := mul_le_mul_of_nonneg_left hl (show 0≤2048000000*κ by positivity)
  have hp := I.matrix_bound
  change (I.runCircuit.matrixQueries : ℝ)<_ at hp
  nlinarith

theorem Implementation.execution_matrix_bound (I : Implementation a n κ ŝ ε)
    (hε : 0<ε) (hε1 : ε<1/2) :
    (Repetition.matrixDepth I.execution : ℝ)<267000000000000000*κ*Real.log (1/ε) := by
  have hq : (Repetition.matrixDepth I.execution : ℝ)≤600000*(I.runCircuit.matrixQueries : ℝ) :=
    by exact_mod_cast I.execution_query_depths.1
  nlinarith [I.matrix_bound_log hε hε1]

theorem Implementation.execution_vector_bound (I : Implementation a n κ ŝ ε)
    {s t : ℝ} (h : BudgetParameters (2*κ) t (9*ŝ/8)) (hs : 0<s) (hst : 2*s/3≤t) :
    (I.execution.vectorDepth : ℝ)<216000001800000*(κ/s) := by
  have hq : (I.execution.vectorDepth : ℝ)≤600000*(I.runCircuit.vectorQueries : ℝ) :=
    by exact_mod_cast I.execution_query_depths.2
  have hp := (I.original_scale_bounds h hs hst).1
  change (I.runCircuit.vectorQueries : ℝ)<_ at hp
  nlinarith

end OptimalQLS.PhysicalRobustness.PhysicalProgram
