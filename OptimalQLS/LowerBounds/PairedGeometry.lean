import OptimalQLS.LowerBounds.PureDensity
import OptimalQLS.LowerBounds.SourcePerturbation
import OptimalQLS.LowerBounds.VectorPerturbationScalars
import OptimalQLS.LowerBounds.RealHardFamily

/-! Actual nearby sources, inverse solutions and fixed-direction measurement. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
variable {D : Type*} [Fintype D] [DecidableEq D]

theorem overlap_eq_inner (u v : D → ℂ) : star u ⬝ᵥ v = inner ℂ (WithLp.toLp 2 u) (WithLp.toLp 2 v) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

theorem direction_pure_probability (e v : D → ℂ) :
    (ketBra e e * pureDensity v).trace.re = ‖inner ℂ (WithLp.toLp 2 e) (WithLp.toLp 2 v)‖ ^ 2 := by
  rw [pureDensity, ketBra_mul, Matrix.trace_smul]
  have heq : (ketBra e v).trace = star (star e ⬝ᵥ v) := by
    simp [ketBra, dotProduct, star_sum, mul_comm]
  rw [heq]
  change ((star e ⬝ᵥ v) * star (star e ⬝ᵥ v)).re = _
  simp only [Complex.star_def]
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq, overlap_eq_inner]

def pairedNormalizedSolution (y e : D → ℂ) (alpha : ℝ) : D → ℂ :=
  (Real.sqrt (‖WithLp.toLp 2 y‖ ^ 2 + alpha ^ 2))⁻¹ • (y + alpha • e)

theorem pairedNormalizedSolution_norm (y e : D → ℂ) (alpha : ℝ)
    (hye : inner ℂ (WithLp.toLp 2 y) (WithLp.toLp 2 e) = 0) (he : ‖WithLp.toLp 2 e‖ = 1)
    (ha : 0 < alpha) : ‖WithLp.toLp 2 (pairedNormalizedSolution y e alpha)‖ = 1 := by
  have hsq := orthogonal_real_sum_norm_sq y e alpha hye he
  have hr : 0 < Real.sqrt (‖WithLp.toLp 2 y‖ ^ 2 + alpha ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hnorm : ‖WithLp.toLp 2 (y + alpha • e)‖ = Real.sqrt (‖WithLp.toLp 2 y‖ ^ 2 + alpha ^ 2) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ ‖WithLp.toLp 2 y‖ ^ 2 + alpha ^ 2 by positivity), norm_nonneg (WithLp.toLp 2 (y + alpha • e))]
  change ‖(Real.sqrt (‖WithLp.toLp 2 y‖ ^ 2 + alpha ^ 2))⁻¹ • WithLp.toLp 2 (y + alpha • e)‖ = 1
  rw [norm_smul, hnorm, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']

theorem pairedNormalizedSolution_direction_probability (y e : D → ℂ) (alpha : ℝ)
    (hye : inner ℂ (WithLp.toLp 2 y) (WithLp.toLp 2 e) = 0) (he : ‖WithLp.toLp 2 e‖ = 1)
    (ha : 0 < alpha) :
    (ketBra e e * pureDensity (pairedNormalizedSolution y e alpha)).trace.re =
      alpha ^ 2 / (‖WithLp.toLp 2 y‖ ^ 2 + alpha ^ 2) := by
  rw [direction_pure_probability]
  have hey : inner ℂ (WithLp.toLp 2 e) (WithLp.toLp 2 y) = 0 := by rw [← inner_conj_symm, hye]; simp
  have hee : inner ℂ (WithLp.toLp 2 e) (WithLp.toLp 2 e) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, he]; norm_num
  change ‖inner ℂ (WithLp.toLp 2 e) ((Real.sqrt (‖WithLp.toLp 2 y‖ ^ 2 + alpha ^ 2))⁻¹ •
    (WithLp.toLp 2 y + alpha • WithLp.toLp 2 e))‖ ^ 2 = _
  rw [inner_smul_right_eq_smul, inner_add_right, inner_smul_right_eq_smul, hey, hee]
  simp only [zero_add, norm_smul, norm_one, Real.norm_eq_abs, mul_one, mul_pow, sq_abs, inv_pow]
  rw [Real.sq_sqrt (by positivity)]
  ring

theorem inverse_eigen_direction (M : Matrix D D ℂ) (e : D → ℂ) {kappa : ℝ}
    (hk : kappa ≠ 0) (hM : IsUnit M) (he : M *ᵥ e = kappa⁻¹ • e) : M⁻¹ *ᵥ e = kappa • e := by
  have hi := Matrix.nonsing_inv_mul M ((Matrix.isUnit_iff_isUnit_det M).mp hM)
  have hv : M⁻¹ *ᵥ (M *ᵥ e) = e := by rw [Matrix.mulVec_mulVec, hi, Matrix.one_mulVec]
  rw [he, Matrix.mulVec_smul] at hv
  have h := congrArg (fun v : D → ℂ => kappa • v) hv
  simpa only [smul_smul, mul_inv_cancel₀ hk, one_smul] using h

theorem perturbedSource_norm (b e : D → ℂ) (tau : ℝ)
    (hb : ‖WithLp.toLp 2 b‖ = 1) (he : ‖WithLp.toLp 2 e‖ = 1)
    (hbe : inner ℂ (WithLp.toLp 2 b) (WithLp.toLp 2 e) = 0) :
    ‖WithLp.toLp 2 (perturbedSource b e tau)‖ = 1 := by
  have hn := orthogonal_real_sum_norm_sq b e tau hbe he
  rw [hb, one_pow] at hn
  have hc : 0 < perturbationCos tau := by unfold perturbationCos; positivity
  have hcs : perturbationCos tau ^ 2 * (1 + tau ^ 2) = 1 := by
    have h := perturbation_trigonometry tau
    unfold perturbationSin at h
    nlinarith
  change ‖perturbationCos tau • WithLp.toLp 2 (b + tau • e)‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have hnorm := norm_nonneg (WithLp.toLp 2 (b + tau • e))
  nlinarith [mul_nonneg hc.le hnorm]

theorem inverse_perturbedSource (M : Matrix D D ℂ) (b e : D → ℂ) (kappa tau : ℝ)
    (he : M⁻¹ *ᵥ e = kappa • e) :
    M⁻¹ *ᵥ perturbedSource b e tau = perturbationCos tau • (M⁻¹ *ᵥ b + (tau * kappa) • e) := by
  simp only [perturbedSource, Matrix.mulVec_smul, Matrix.mulVec_add, he, smul_smul]

/-- The literal inverse-vector norm obeys the paper's squared rational formula. -/
theorem inverse_perturbedSource_norm_sq (M : Matrix D D ℂ) (b e : D → ℂ) {kappa estimate : ℝ}
    (hk : 0 < kappa) (he : M⁻¹ *ᵥ e = kappa • e) (henorm : ‖WithLp.toLp 2 e‖ = 1)
    (hye : inner ℂ (WithLp.toLp 2 (M⁻¹ *ᵥ b)) (WithLp.toLp 2 e) = 0) :
    ‖WithLp.toLp 2 (M⁻¹ *ᵥ perturbedSource b e (vectorPerturbationSize kappa estimate))‖ ^ 2 =
      pairedSolutionNormSquared kappa estimate ‖WithLp.toLp 2 (M⁻¹ *ᵥ b)‖ := by
  let tau := vectorPerturbationSize kappa estimate
  have hta : tau * kappa = 5 * estimate / 4 := by dsimp [tau, vectorPerturbationSize]; field_simp
  rw [inverse_perturbedSource M b e kappa tau he, hta]
  change ‖perturbationCos tau • WithLp.toLp 2 (M⁻¹ *ᵥ b + (5 * estimate / 4) • e)‖ ^ 2 = _
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    orthogonal_real_sum_norm_sq _ e _ hye henorm]
  simp only [perturbationCos, inv_pow, Real.sq_sqrt (show 0 ≤ 1 + tau ^ 2 by positivity)]
  dsimp [pairedSolutionNormSquared, tau, vectorPerturbationSize]
  field_simp
  ring

end OptimalQLS.LowerBounds
