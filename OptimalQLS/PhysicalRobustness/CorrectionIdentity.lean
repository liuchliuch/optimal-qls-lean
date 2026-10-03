import OptimalQLS.PhysicalRobustness.Correction

/-! Exact high-spectrum graph-to-solution identity for the noisy correction. -/
noncomputable section
namespace OptimalQLS.PhysicalRobustness
open Geometry PolynomialTransform Preparation Alignment GraphEncoding Matrix Refinement
variable {D : Type*} [Fintype D] [DecidableEq D]

theorem highCorrection_projectedGraph (B : Matrix D D ℂ) (hB : B.IsHermitian)
    {κ δ : ℝ} (hκ : 0<κ) (hδ : 0≤δ) (b : EuclideanSpace ℂ D) :
    highCorrection (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) B)
      (matrixHermitian_symmetric B hB) κ δ
      (graphCoordinate 2 (Alignment.kernelProjector (graphMatrix B (2*κ)) (graphInput b))) =
      ((1/(8*κ) : ℝ) : ℂ) • highInverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) B)
        (matrixHermitian_symmetric B hB) δ b := by
  rw [projectedGraph_coordinate B hB (by positivity : 0<2*κ),map_smul]
  have h := congrArg (fun T : EuclideanSpace ℂ D →L[ℂ] EuclideanSpace ℂ D => T b)
    (highCorrection_resolvent_identity (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) B)
      (matrixHermitian_symmetric B hB) hκ hδ)
  change highCorrection _ _ κ δ ((Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) B)
      (Ring.inverse ((Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) B)^2+
        (((2*κ)⁻¹)^2 : ℂ) • (1 : EuclideanSpace ℂ D →L[ℂ] EuclideanSpace ℂ D)) b)) =
    (1/4 : ℂ) • highInverse _ _ δ b at h
  rw [h,smul_smul]
  congr 1
  push_cast
  ring

theorem highCorrection_normalized_kernel (B : Matrix D D ℂ) (hB : B.IsHermitian)
    {κ δ : ℝ} (hκ : 0<κ) (hδ : 0≤δ) (b : EuclideanSpace ℂ D)
    (hv : highInverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) B)
      (matrixHermitian_symmetric B hB) δ b≠0) (β : ℝ) :
    let H := graphMatrix B (2*κ)
    let γ := ‖Alignment.kernelProjector H (graphInput b)‖
    let v := highInverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) B)
      (matrixHermitian_symmetric B hB) δ b
    highCorrection (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) B)
      (matrixHermitian_symmetric B hB) κ δ
      (β • graphCoordinate 2 (normalizedProjectedInput H (graphInput b))) =
      (β*‖v‖/(8*κ*γ)) • NormedSpace.normalize v := by
  let T := Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) B
  let H := graphMatrix B (2*κ)
  let γ := ‖Alignment.kernelProjector H (graphInput b)‖
  let v := highInverse T (matrixHermitian_symmetric B hB) δ b
  let C := highCorrection T (matrixHermitian_symmetric B hB) κ δ
  have hvn : ‖v‖≠0 := norm_ne_zero_iff.mpr hv
  have hp : C (graphCoordinate 2 (Alignment.kernelProjector H (graphInput b)))=(1/(8*κ) : ℝ) • v := by
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ)] using highCorrection_projectedGraph B hB hκ hδ b
  have mapreal (L : EuclideanSpace ℂ D →L[ℂ] EuclideanSpace ℂ D) (r : ℝ) (x : EuclideanSpace ℂ D) :
      L (r • x)=r • L x := L.toLinearMap.map_smul_of_tower r x
  have hg : graphCoordinate 2 (normalizedProjectedInput H (graphInput b))=
      γ⁻¹ • graphCoordinate 2 (Alignment.kernelProjector H (graphInput b)) :=
    (graphCoordinate (D := D) 2).toLinearMap.map_smul_of_tower _ _
  change C (β • graphCoordinate 2 (normalizedProjectedInput H (graphInput b))) =
    (β*‖v‖/(8*κ*γ)) • NormedSpace.normalize v
  rw [hg,mapreal,mapreal,hp,NormedSpace.normalize,smul_smul,smul_smul,smul_smul]
  congr 1
  field_simp

end OptimalQLS.PhysicalRobustness
