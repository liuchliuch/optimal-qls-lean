import OptimalQLS.PolynomialTransform.Spectral
import OptimalQLS.Geometry.MoorePenrose
import OptimalQLS.BlockEncoding

/-! # Canonical Moore–Penrose inverse for finite Hermitian matrices

This construction uses the proved orthonormal spectral theorem. It does not
accept an inverse or a kernel-projector certificate as an input.
-/
noncomputable section
namespace OptimalQLS
open Geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

def hermitianPseudoInverse (H : E →L[ℂ] E) (hH : H.toLinearMap.IsSymmetric) : E →L[ℂ] E :=
  conjugate (hH.eigenvectorBasis rfl).repr
    (diagonal (fun i => ((hH.eigenvalues rfl i)⁻¹ : ℝ)))

theorem hermitian_mul_pseudoInverse (H : E →L[ℂ] E) (hH : H.toLinearMap.IsSymmetric) :
    H * hermitianPseudoInverse H hH =
      1 - (LinearMap.ker H.toLinearMap).starProjection := by
  let U := (hH.eigenvectorBasis rfl).repr
  let a := hH.eigenvalues rfl
  have hd : ∀ x i, U (H x) i = (a i : ℂ) * U x i :=
    fun x i => hH.eigenvectorBasis_apply_self_apply rfl x i
  rw [PolynomialTransform.kernel_projection_coordinates U H a hd]
  conv_lhs => lhs; rw [operator_eq_conjugate U H a hd]
  change conjugate U (diagonal (fun i => (a i : ℂ))) *
    conjugate U (diagonal (fun i => ((a i)⁻¹ : ℝ))) = _
  rw [← map_mul, ← map_one (conjugate U), ← map_sub]
  congr 1
  apply ContinuousLinearMap.ext
  intro x
  ext i
  by_cases hi : a i = 0 <;>
    simp [diagonal_apply, PolynomialTransform.zeroIndicator, hi, mul_assoc]

/-- The inverse constructed above is Hermitian. -/
theorem hermitianPseudoInverse_symmetric (H : E →L[ℂ] E)
    (hH : H.toLinearMap.IsSymmetric) :
    (hermitianPseudoInverse H hH).toLinearMap.IsSymmetric := by
  exact conjugate_symmetric _ _ (diagonal_real_symmetric _)

theorem pseudoInverse_mul_hermitian (H : E →L[ℂ] E) (hH : H.toLinearMap.IsSymmetric) :
    hermitianPseudoInverse H hH * H =
      1 - (LinearMap.ker H.toLinearMap).starProjection := by
  exact symmetric_reverse_product _ _ _ hH (hermitianPseudoInverse_symmetric H hH)
    (LinearMap.IsSymmetric.id.sub (LinearMap.ker H.toLinearMap).starProjection_isSymmetric)
    (hermitian_mul_pseudoInverse H hH)

theorem hermitian_mul_kernel (H : E →L[ℂ] E) :
    H * (LinearMap.ker H.toLinearMap).starProjection = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  exact (LinearMap.ker H.toLinearMap).starProjection_apply_mem x

theorem hermitianPseudoInverse_mul_kernel (H : E →L[ℂ] E)
    (hH : H.toLinearMap.IsSymmetric) :
    hermitianPseudoInverse H hH * (LinearMap.ker H.toLinearMap).starProjection = 0 := by
  let U := (hH.eigenvectorBasis rfl).repr
  let a := hH.eigenvalues rfl
  have hd : ∀ x i, U (H x) i = (a i : ℂ) * U x i :=
    fun x i => hH.eigenvectorBasis_apply_self_apply rfl x i
  rw [PolynomialTransform.kernel_projection_coordinates U H a hd]
  change conjugate U (diagonal (fun i => ((a i)⁻¹ : ℝ))) *
    conjugate U (diagonal (fun i => (PolynomialTransform.zeroIndicator a i : ℂ))) = 0
  rw [← map_mul, ← map_zero (conjugate U)]
  congr 1
  apply ContinuousLinearMap.ext
  intro x
  ext i
  by_cases hi : a i = 0 <;> simp [PolynomialTransform.zeroIndicator, hi]

/-- All four Moore–Penrose equations, derived for the constructed inverse. -/
theorem hermitianPseudoInverse_moore_penrose (H : E →L[ℂ] E)
    (hH : H.toLinearMap.IsSymmetric) :
    H * hermitianPseudoInverse H hH * H = H ∧
    hermitianPseudoInverse H hH * H * hermitianPseudoInverse H hH =
      hermitianPseudoInverse H hH ∧
    (H * hermitianPseudoInverse H hH).toLinearMap.IsSymmetric ∧
    (hermitianPseudoInverse H hH * H).toLinearMap.IsSymmetric := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mul_assoc, pseudoInverse_mul_hermitian, mul_sub, mul_one, hermitian_mul_kernel,
      sub_zero]
  · rw [mul_assoc, hermitian_mul_pseudoInverse, mul_sub, mul_one,
      hermitianPseudoInverse_mul_kernel, sub_zero]
  · rw [hermitian_mul_pseudoInverse]
    exact LinearMap.IsSymmetric.id.sub (LinearMap.ker H.toLinearMap).starProjection_isSymmetric
  · rw [pseudoInverse_mul_hermitian]
    exact LinearMap.IsSymmetric.id.sub (LinearMap.ker H.toLinearMap).starProjection_isSymmetric

/-- The general canonical construction agrees with the explicit auxiliary
pseudoinverse already used in Lemma 4.2, by the proved four-equation uniqueness. -/
theorem hermitianPseudoInverse_auxiliary_eq (A : E →L[ℂ] E)
    (hA : A.toLinearMap.IsSymmetric) {κ : ℝ} (hκ : 0 < κ) :
    hermitianPseudoInverse (blockAuxiliary A κ⁻¹)
      (lemma42_auxiliary_hermitian A hA κ⁻¹) = auxiliaryPseudoInverse A hA κ⁻¹ := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := hermitianPseudoInverse_moore_penrose (blockAuxiliary A κ⁻¹)
    (lemma42_auxiliary_hermitian A hA κ⁻¹)
  exact lemma42_pseudoinverse_unique A hA hκ _ h₁ h₂ h₃ h₄

end OptimalQLS
