import OptimalQLS.Refinement.CorrectionIdentity
import OptimalQLS.PolynomialTransform.RefinementTheorems

noncomputable section
namespace OptimalQLS.Refinement
open Matrix Preparation GraphEncoding PolynomialTransform
open scoped Matrix.Norms.L2Operator
variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Actual polynomial correction, as an operator on the original data space. -/
def correctionOperator (A : Matrix D D ℂ) (κ η : ℝ) :
    EuclideanSpace ℂ D →L[ℂ] EuclideanSpace ℂ D :=
  Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)
    (Polynomial.aeval A (liftReal (paperCorrectionPolynomial κ η)))

theorem correctionOperator_norm (A : Matrix D D ℂ) (hA : A.IsHermitian)
    (hAnorm : ‖A‖≤1) {κ η : ℝ} (hκ : 2≤κ) (hη : 0<η) :
    ‖correctionOperator A κ η‖≤3/4 := lemma55_correction_matrix_norm A hA hAnorm hκ hη

theorem correctionOperator_error (A : Matrix D D ℂ) (hA : A.IsHermitian) (hunit : IsUnit A)
    (hAnorm : ‖A‖≤1) {κ η : ℝ} (hκ : 2≤κ) (hη : 0<η) (hη1 : η<1/2)
    (hinorm : ‖Ring.inverse A‖≤κ) :
    ‖correctionOperator A κ η-exactCorrection (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) κ‖≤η/2 := by
  have he := lemma55_correction_matrix_error A hA hunit hκ hη hη1 hAnorm hinorm
  let φ := Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)
  have hD : φ ((1/4 : ℂ) • (1+((κ⁻¹)^2 : ℂ) • (Ring.inverse A)^2))=
      exactCorrection (φ A) κ := by
    simp only [map_smul,map_add,map_one,map_pow,exactCorrection]
    rw [Perturbation.toEuclideanCLM_inverse A hunit]
  change ‖φ (Polynomial.aeval A (liftReal (paperCorrectionPolynomial κ η)))-exactCorrection (φ A) κ‖≤η/2
  rw [← hD,← map_sub]
  exact he

/-- Analytic joint-branch guarantee. The filter error is supplied by its
proved polynomial block implementation; the correction is the literal
constructed polynomial, not an assumed inverse transform. -/
theorem refinement_component_guarantee (A : Matrix D D ℂ) (hA : A.IsHermitian)
    (hunit : IsUnit A) (hAnorm : ‖A‖≤1) {κ ε : ℝ} (hκ : 2≤κ)
    (hinorm : ‖Ring.inverse A‖≤κ) (hε0 : 0<ε) (hε1 : ε<1/2)
    (b : EuclideanSpace ℂ D) (hb : ‖b‖=1)
    (y : EuclideanSpace ℂ (Fin 4 × D)) (hy : ‖y‖≤1) {β : ℝ} (hβ0 : 1/32≤β) (hβ1 : β≤1)
    (hPy : Alignment.kernelProjector (graphMatrix A κ) y=
      β • Alignment.normalizedProjectedInput (graphMatrix A κ) (graphInput b))
    (F : EuclideanSpace ℂ (Fin 4 × D) →L[ℂ] EuclideanSpace ℂ (Fin 4 × D))
    (hF : ‖F-Alignment.kernelProjector (graphMatrix A κ)‖≤ε/1024) :
    let z := correctionOperator A κ (ε/1024) (graphCoordinate 2 (F y))
    let x := NormedSpace.normalize (Ring.inverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) b)
    z≠0 ∧ ‖NormedSpace.normalize z-x‖≤ε/2 ∧ 1/65536<‖z‖^2 := by
  let T := Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A
  let H := graphMatrix A κ
  let P := Alignment.kernelProjector H
  let u := Alignment.normalizedProjectedInput H (graphInput b)
  let γ := ‖P (graphInput b)‖
  let v := Ring.inverse T b
  let s := ‖v‖
  let x := NormedSpace.normalize v
  let η := ε/1024
  let C := correctionOperator A κ η
  let C₀ := exactCorrection T κ
  let y₀ := β • graphCoordinate 2 u
  let lam := β*s/(4*κ*γ)
  have hk : 0<κ := by linarith
  have heta : 0<η := by dsimp [η]; positivity
  have heta1 : η<1/2 := by dsimp [η]; linarith
  have hTu : IsUnit T := hunit.map (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)).toMonoidHom
  have hTi : ‖Ring.inverse T‖≤κ := by rw [← Perturbation.toEuclideanCLM_inverse A hunit]; exact hinorm
  have hv : v≠0 := Perturbation.inverse_apply_ne_zero T hTu (by intro hz; simp [hz] at hb)
  have hs : 0<s := norm_pos_iff.mpr hv
  have hp := graphInput_promises A hA hTu hk hAnorm hTi b hb
  have hγ : 0<γ := by
    have hpos := hp.2.2.2.1
    change 0<γ^2 at hpos
    have hnon : 0≤γ := norm_nonneg _
    nlinarith
  have hγb : γ≤s/κ := by
    apply (sq_le_sq₀ (norm_nonneg _) (div_nonneg hs.le hk.le)).mp
    simpa only [div_pow] using hp.2.2.1
  have hlam : 1/128≤lam := correction_amplitude_lower hβ0 hs hk hγ hγb
  have hu : ‖u‖=1 := NormedSpace.norm_normalize (norm_pos_iff.mp hγ)
  have hy₀ : ‖y₀‖≤1 := by
    have hgu := (graphCoordinate_norm_le 2 u).trans_eq hu
    dsimp only [y₀]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤β)]
    exact (mul_le_mul_of_nonneg_left hgu (by linarith)).trans (by simpa using hβ1)
  have hm (L : EuclideanSpace ℂ (Fin 4 × D) →L[ℂ] EuclideanSpace ℂ D) (a : ℝ) (v) :
      L (a • v)=a • L v := L.toLinearMap.map_smul_of_tower a v
  have hd : graphCoordinate 2 (F y)-y₀=graphCoordinate 2 ((F-P) y) := by
    rw [ContinuousLinearMap.sub_apply,map_sub,hPy,hm]
  have hyerr : ‖graphCoordinate 2 (F y)-y₀‖≤η := by
    rw [hd]
    calc
      ‖graphCoordinate 2 ((F-P) y)‖≤‖(F-P) y‖ := graphCoordinate_norm_le _ _
      _≤‖F-P‖*‖y‖ := (F-P).le_opNorm _
      _≤η*1 := mul_le_mul hF hy (norm_nonneg _) heta.le
      _=η := mul_one _
  have hcorrect : C₀ y₀=lam • x := exactCorrection_normalized_kernel A hA hTu hk hAnorm hTi b hb β
  have hC : ‖C.restrictScalars ℝ‖≤3/4 := by
    rw [ContinuousLinearMap.norm_restrictScalars]
    exact correctionOperator_norm A hA hAnorm hκ heta
  have hCD : ‖C.restrictScalars ℝ-C₀.restrictScalars ℝ‖≤η/2 := by
    change ‖(C-C₀).restrictScalars ℝ‖≤η/2
    rw [ContinuousLinearMap.norm_restrictScalars]
    exact correctionOperator_error A hA hunit hAnorm hκ heta heta1 hinorm
  have hz := correction_filter_error (C.restrictScalars ℝ) (C₀.restrictScalars ℝ)
    (graphCoordinate 2 (F y)) y₀ x heta.le hC hCD hyerr hy₀ hcorrect
  exact refinement_state_and_probability x (C (graphCoordinate 2 (F y)))
    (NormedSpace.norm_normalize hv) hε0 hε1 hlam hz

end OptimalQLS.Refinement
