import OptimalQLS.HermitianPseudoInverse

noncomputable section
namespace OptimalQLS
variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The exact orthogonal projector onto the actual matrix kernel. -/
def matrixKernelProjection (H : Matrix D D ℂ) : Matrix D D ℂ :=
  (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)).symm
    (LinearMap.ker (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H).toLinearMap).starProjection

theorem matrixHermitian_symmetric (H : Matrix D D ℂ) (hH : star H = H) :
    (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H).toLinearMap.IsSymmetric := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
  exact (show IsSelfAdjoint H from hH).map (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ))

/-- A canonical inverse, transported from the actual spectral construction. -/
def matrixPseudoInverse (H : Matrix D D ℂ) (hH : star H = H) : Matrix D D ℂ :=
  (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)).symm
    (hermitianPseudoInverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H)
      (matrixHermitian_symmetric H hH))

theorem matrix_mul_kernel (H : Matrix D D ℂ) : H * matrixKernelProjection H = 0 := by
  let φ := Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)
  apply φ.injective
  rw [map_mul, map_zero]
  change φ H * φ (φ.symm (LinearMap.ker (φ H).toLinearMap).starProjection) = 0
  rw [φ.apply_symm_apply]
  exact hermitian_mul_kernel (φ H)

theorem matrix_mul_pseudoInverse (H : Matrix D D ℂ) (hH : star H = H) :
    H * matrixPseudoInverse H hH = 1 - matrixKernelProjection H := by
  let φ := Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)
  apply φ.injective
  rw [map_mul, map_sub, map_one]
  change φ H * φ (φ.symm (hermitianPseudoInverse (φ H) (matrixHermitian_symmetric H hH))) =
    1 - φ (φ.symm (LinearMap.ker (φ H).toLinearMap).starProjection)
  rw [φ.apply_symm_apply, φ.apply_symm_apply]
  exact hermitian_mul_pseudoInverse (φ H) (matrixHermitian_symmetric H hH)

end OptimalQLS
