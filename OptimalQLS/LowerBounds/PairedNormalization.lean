import OptimalQLS.LowerBounds.PairedHardFamily

/-! Identification of the paired target with the literal normalized inverse. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
variable {D : Type*} [Fintype D] [DecidableEq D]

theorem normalize_positive_smul_orthogonal_sum (y e : D → ℂ) (alpha c : ℝ)
    (hye : inner ℂ (WithLp.toLp 2 y) (WithLp.toLp 2 e) = 0) (he : ‖WithLp.toLp 2 e‖ = 1)
    (ha : 0 < alpha) (hc : 0 < c) :
    ‖WithLp.toLp 2 (c • (y + alpha • e))‖⁻¹ • (c • (y + alpha • e)) = pairedNormalizedSolution y e alpha := by
  have hsq := orthogonal_real_sum_norm_sq y e alpha hye he
  have hr : 0 < Real.sqrt (‖WithLp.toLp 2 y‖ ^ 2 + alpha ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hnorm : ‖WithLp.toLp 2 (y + alpha • e)‖ = Real.sqrt (‖WithLp.toLp 2 y‖ ^ 2 + alpha ^ 2) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ ‖WithLp.toLp 2 y‖ ^ 2 + alpha ^ 2 by positivity), norm_nonneg (WithLp.toLp 2 (y + alpha • e))]
  have hscaled : ‖WithLp.toLp 2 (c • (y + alpha • e))‖ = c * Real.sqrt (‖WithLp.toLp 2 y‖ ^ 2 + alpha ^ 2) := by
    change ‖c • WithLp.toLp 2 (y + alpha • e)‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, hnorm]
  rw [hscaled, smul_smul]
  have hcoeff : (c * Real.sqrt (‖WithLp.toLp 2 y‖ ^ 2 + alpha ^ 2))⁻¹ * c =
      (Real.sqrt (‖WithLp.toLp 2 y‖ ^ 2 + alpha ^ 2))⁻¹ := by field_simp
  rw [hcoeff]
  rfl

theorem hardFamilyPairedSolution_eq_normalized_inverse {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (z : BitString m) :
    hardFamilyPairedSolution N kappa estimate z =
      ‖WithLp.toLp 2 ((hardFamilyMatrix N kappa z)⁻¹ *ᵥ hardFamilyPerturbedSource N m kappa estimate)‖⁻¹ •
        ((hardFamilyMatrix N kappa z)⁻¹ *ᵥ hardFamilyPerturbedSource N m kappa estimate) := by
  have ht : vectorPerturbationSize kappa estimate * kappa = 5 * estimate / 4 := by
    unfold vectorPerturbationSize
    field_simp
  have hc : 0 < perturbationCos (vectorPerturbationSize kappa estimate) := by
    unfold perturbationCos; positivity
  have hv := inverse_perturbedSource (hardFamilyMatrix N kappa z) (hardFamilySource N m kappa estimate)
    dilatedLastDirection kappa (vectorPerturbationSize kappa estimate) (hardFamily_direction_inverse hk z)
  rw [ht] at hv
  unfold hardFamilyPairedSolution hardFamilyPerturbedSource
  rw [hv]
  exact (normalize_positive_smul_orthogonal_sum
    ((hardFamilyMatrix N kappa z)⁻¹ *ᵥ hardFamilySource N m kappa estimate)
    dilatedLastDirection (5 * estimate / 4) (perturbationCos (vectorPerturbationSize kappa estimate))
    (hardFamily_solution_orthogonal_direction (N := N) hk estimate z)
    dilatedLastDirection_norm (by linarith) hc).symm


end OptimalQLS.LowerBounds
