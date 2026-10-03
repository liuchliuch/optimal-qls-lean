import OptimalQLS.Geometry.MoorePenrose

noncomputable section
namespace OptimalQLS.Geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- The canonical pseudoinverse has the exact complementary-kernel product,
in the original Hilbert-space coordinates. -/
theorem auxiliary_mul_pseudoinverse_original (A : E →L[ℂ] E)
    (hA : A.toLinearMap.IsSymmetric) {κ : ℝ} (hκ : 0 < κ) :
    blockAuxiliary A κ⁻¹ * auxiliaryPseudoInverse A hA κ⁻¹ =
      1 - (LinearMap.ker (blockAuxiliary A κ⁻¹).toLinearMap).starProjection := by
  let U := (hA.eigenvectorBasis rfl).repr
  let a := hA.eigenvalues rfl
  have hd : ∀ x i, U (A x) i = (a i : ℂ) * U x i :=
    fun x i => hA.eigenvectorBasis_apply_self_apply rfl x i
  rw [original_kernel_projection U A a hd (inv_pos.mpr hκ),
    blockAuxiliary_eq_conjugate U A a hd]
  change conjugate (tripleCoordinates U) (auxiliary a κ⁻¹) *
    conjugate (tripleCoordinates U) (pseudoInverse a κ⁻¹) = _
  rw [← map_mul, auxiliary_mul_pseudoInverse a (inv_pos.mpr hκ), map_sub, map_one]

/-- Kernel vectors are literally annihilated, without a spectral promise. -/
theorem auxiliary_mul_kernel_projection (A : E →L[ℂ] E) (t : ℝ) :
    blockAuxiliary A t *
      (LinearMap.ker (blockAuxiliary A t).toLinearMap).starProjection = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  exact (LinearMap.ker (blockAuxiliary A t).toLinearMap).starProjection_apply_mem x

end OptimalQLS.Geometry
