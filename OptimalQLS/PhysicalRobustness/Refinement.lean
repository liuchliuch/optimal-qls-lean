import OptimalQLS.PhysicalRobustness.CorrectionIdentity
import OptimalQLS.PhysicalRobustness.RefinementBounds
import OptimalQLS.PhysicalRobustness.RefinementGeometry

/-! The actual noisy polynomial refinement branch, with original input
promises discharging all spectral and success-amplitude facts. -/
noncomputable section
namespace OptimalQLS.PhysicalRobustness
open PhysicalPadding Geometry Preparation PolynomialTransform Alignment GraphEncoding Matrix Refinement
open scoped Matrix.Norms.L2Operator
variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

def noisyCorrectionOperator (B : Matrix P P ℂ) (κ η : ℝ) :
    EuclideanSpace ℂ P →L[ℂ] EuclideanSpace ℂ P :=
  polynomialOperator (noisyCorrectionPolynomial κ η) (Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) B)

/-- Quantitative accepting component of the noisy refinement.  Its filter
operator is the actual branch of the implemented filter in the subsequent
circuit theorem; no algorithmic error certificate is postulated here. -/
theorem noisy_refinement_component_guarantee (f : D ↪ P)
    (A : Matrix D D ℂ) (hA : A.IsHermitian) (hunit : IsUnit A) (hAnorm : ‖A‖≤1)
    (B : Matrix P P ℂ) (hB : B.IsHermitian) (hBn : ‖B‖≤1)
    (b : EuclideanSpace ℂ D) (hb : ‖b‖=1)
    {κ δ ŝ ε : ℝ} (hκ : 2≤κ) (hδ : 0≤δ) (hinv : ‖Ring.inverse A‖≤κ)
    (hpert : ‖B-zeroExtend f A‖≤δ) (hsmall : κ*δ≤1/4)
    (hestlo : solutionScale 1 A b/2≤ŝ) (hesthi : ŝ≤2*solutionScale 1 A b)
    (hε : 0<ε) (hε1 : ε<1/2)
    (y : EuclideanSpace ℂ (Fin 4 × P)) (hy : ‖y‖≤1)
    {β : ℝ} (hβ0 : 1/32≤β) (hβ1 : β≤1)
    (hPy : Alignment.kernelProjector (graphMatrix B (2*κ)) y=
      β • normalizedProjectedInput (graphMatrix B (2*κ)) (graphInput (coordinateIsometry f b)))
    (F : EuclideanSpace ℂ (Fin 4 × P) →L[ℂ] EuclideanSpace ℂ (Fin 4 × P))
    (hF : ‖F-Alignment.kernelProjector (graphMatrix B (2*κ))‖≤ε/4096) :
    let z := noisyCorrectionOperator B κ (ε/4096) (graphCoordinate 2 (F y))
    let v := highInverse (Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) B)
      (matrixHermitian_symmetric B hB) δ (coordinateIsometry f b)
    z≠0 ∧ ‖NormedSpace.normalize z-NormedSpace.normalize v‖≤ε/2 ∧
      1/262144<‖z‖^2 := by
  let T := Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) B
  let hT := matrixHermitian_symmetric B hB
  let H := graphMatrix B (2*κ)
  let Q := Alignment.kernelProjector H
  let u := normalizedProjectedInput H (graphInput (coordinateIsometry f b))
  let γ := ‖Q (graphInput (coordinateIsometry f b))‖
  let v := highInverse T hT δ (coordinateIsometry f b)
  let x := NormedSpace.normalize v
  let η := ε/4096
  let C := noisyCorrectionOperator B κ η
  let C₀ := highCorrection T hT κ δ
  let y₀ := β • graphCoordinate 2 u
  let lam := β*‖v‖/(8*κ*γ)
  have hk : 0<κ := by linarith
  have heta : 0<η := by dsimp [η]; positivity
  have heta1 : η<1/2 := by dsimp [η]; linarith
  have hgeom := noisy_refinement_geometry f A hA hunit hAnorm B hB hBn b hb
    hκ hδ hinv hpert hsmall hestlo hesthi
  have hv : v≠0 := hgeom.1
  have hg : 0<γ := hgeom.2.1
  have hgb : γ≤3*‖v‖/(2*κ) := hgeom.2.2.1
  have hlam : 1/384≤lam := by
    have hs : 0<‖v‖ := norm_pos_iff.mpr hv
    have hkg := (le_div_iff₀ (by positivity : (0:ℝ)<2*κ)).mp hgb
    apply (le_div_iff₀ (by positivity : (0:ℝ)<8*κ*γ)).mpr
    nlinarith
  have hu : ‖u‖=1 := NormedSpace.norm_normalize (norm_pos_iff.mp hg)
  have hy₀ : ‖y₀‖≤1 := by
    have hgu := (graphCoordinate_norm_le 2 u).trans_eq hu
    dsimp only [y₀]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤β)]
    exact (mul_le_mul_of_nonneg_left hgu (by linarith)).trans (by simpa using hβ1)
  have hm (L : EuclideanSpace ℂ (Fin 4 × P) →L[ℂ] EuclideanSpace ℂ P) (r : ℝ) (v) :
      L (r • v)=r • L v := L.toLinearMap.map_smul_of_tower r v
  have hd : graphCoordinate 2 (F y)-y₀=graphCoordinate 2 ((F-Q) y) := by
    rw [ContinuousLinearMap.sub_apply,map_sub,hPy,hm]
  have herr : ‖graphCoordinate 2 (F y)-y₀‖≤η := by
    rw [hd]
    calc
      _ ≤ ‖(F-Q) y‖ := graphCoordinate_norm_le _ _
      _ ≤ ‖F-Q‖*‖y‖ := (F-Q).le_opNorm _
      _ ≤ η*1 := mul_le_mul hF hy (norm_nonneg _) heta.le
      _ = η := mul_one _
  have hcorrect : C₀ y₀=lam • x := highCorrection_normalized_kernel B hB hk hδ
    (coordinateIsometry f b) hv β
  have hC : ‖C.restrictScalars ℝ‖≤3/4 := by
    rw [ContinuousLinearMap.norm_restrictScalars]
    exact noisyCorrection_operator_norm T hT hBn hκ heta heta1
  have hCD : ‖C.restrictScalars ℝ-C₀.restrictScalars ℝ‖≤5*η/4 := by
    change ‖(C-C₀).restrictScalars ℝ‖≤5*η/4
    rw [ContinuousLinearMap.norm_restrictScalars]
    exact noisyCorrection_operator_error T hT hBn hκ hδ hsmall heta heta1 hgeom.2.2.2
  have hz := noisy_correction_filter_error (C.restrictScalars ℝ) (C₀.restrictScalars ℝ)
    (graphCoordinate 2 (F y)) y₀ x heta.le hC hCD herr hy₀ hcorrect
  exact noisy_refinement_state_and_probability x (C (graphCoordinate 2 (F y)))
    (NormedSpace.norm_normalize hv) hε hε1 hlam hz

end OptimalQLS.PhysicalRobustness
