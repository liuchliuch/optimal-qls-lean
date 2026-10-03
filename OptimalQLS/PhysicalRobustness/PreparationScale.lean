import OptimalQLS.Preparation.Parameters

/-! An analysis-only scale allowing the existing finite preparation circuit
to be reused with the noisy graph, without knowing its spectral data. -/
noncomputable section
namespace OptimalQLS.PhysicalRobustness
open Preparation TransducerCompiler

/-- This scale is used only in the proof, never as input to the circuit. -/
def noisyAnalysisScale (w ŝ : ℝ) : ℝ := max 1 (max w (9*ŝ/20))

/-- All existing preparation budget and overlap-scale premises follow from
constant-factor regularized-norm bounds. The actual supplied estimate is
rescaled by the fixed factor 9/8. -/
theorem noisyAnalysisScale_bounds {κ s ŝ w : ℝ}
    (hκ : 2 ≤ κ) (hs : 1 ≤ s) (hsκ : s ≤ κ)
    (hestlo : s/2 ≤ ŝ) (hesthi : ŝ ≤ 2*s)
    (hw0 : 0 ≤ w) (hwlo : 2*s/3 ≤ w) (hwhi : w ≤ 3*s/2)
    (hwunit : 1 ≤ 2*w^2) :
    BudgetParameters (2*κ) (noisyAnalysisScale w ŝ) (9*ŝ/8) ∧
      w ≤ noisyAnalysisScale w ŝ ∧
      (noisyAnalysisScale w ŝ)^2 ≤ 2*w^2 ∧
      2*s/3 ≤ noisyAnalysisScale w ŝ := by
  let t := noisyAnalysisScale w ŝ
  have hsh : 0 ≤ ŝ := by linarith
  have ht1 : 1 ≤ t := le_max_left _ _
  have htw : w ≤ t := (le_max_left _ _).trans (le_max_right _ _)
  have htest : 9*ŝ/20 ≤ t := (le_max_right _ _).trans (le_max_right _ _)
  have htupper : t ≤ 2*κ := max_le (by linarith)
    (max_le (by linarith) (by linarith))
  have ht_est : t ≤ 3*ŝ := max_le (by linarith)
    (max_le (by linarith) (by linarith))
  have hbound : BudgetParameters (2*κ) t (9*ŝ/8) :=
    ⟨by linarith, ht1, htupper, by linarith, by linarith⟩
  have hsq : t^2 ≤ 2*w^2 := by
    unfold t noisyAnalysisScale
    rcases le_total 1 (max w (9*ŝ/20)) with h | h
    · rw [max_eq_right h]
      rcases le_total w (9*ŝ/20) with hw | hw
      · rw [max_eq_right hw]
        have he : (9*ŝ/20)^2 ≤ (9*s/10)^2 :=
          (sq_le_sq₀ (by positivity) (by linarith)).mpr (by linarith)
        have hwl : (2*s/3)^2 ≤ w^2 :=
          (sq_le_sq₀ (by linarith) hw0).mpr hwlo
        nlinarith
      · rw [max_eq_left hw]
        nlinarith [sq_nonneg w]
    · rw [max_eq_left h]
      simpa using hwunit
  exact ⟨hbound,htw,hsq,hwlo.trans htw⟩

/-- The actual selected preparation program is independent of the analysis
scale and is fixed solely by κ and the supplied norm estimate. -/
theorem noisy_selected_preparation_eq
    {S D : Type*} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]
    (s₀ : S) (i₀ : D) {κ s ŝ w : ℝ}
    (h : BudgetParameters (2*κ) (noisyAnalysisScale w ŝ) (9*ŝ/8)) :
    selectedPreparationCircuit s₀ i₀ h.kappa_ge_two
      (classical_parameter_range h).1 (classical_parameter_range h).2 =
      originalPreparationAlgorithm s₀ i₀ h := selectedPreparationCircuit_eq s₀ i₀ h

/-- Vector-query and source-work coefficients transfer back to the original
solution scale with only a universal factor three. -/
theorem noisy_vector_coefficient_transfer {κ s t : ℝ}
    (hκ : 0≤κ) (hs : 0<s) (ht : 2*s/3≤t) : (2*κ)/t≤3*(κ/s) := by
  have ht0 : 0<t := by linarith
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ ht0 hs).mpr
  nlinarith [mul_le_mul_of_nonneg_left ht hκ]

end OptimalQLS.PhysicalRobustness
