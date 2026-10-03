import OptimalQLS.Geometry.Transport

noncomputable section
namespace OptimalQLS.Geometry

section Conjugation
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Unitary coordinate transport, as an actual endomorphism-ring homomorphism. -/
def conjugate (U : E ≃ₗᵢ[ℂ] F) : (F →L[ℂ] F) →+* (E →L[ℂ] E) where
  toFun T := U.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L T ∘L
    U.toContinuousLinearEquiv.toContinuousLinearMap
  map_one' := by ext x; simp
  map_zero' := by ext x; simp
  map_add' := by intros; ext x; simp
  map_mul' := by intros; ext x; simp

@[simp] theorem conjugate_apply (U : E ≃ₗᵢ[ℂ] F) (T : F →L[ℂ] F) (x : E) :
    conjugate U T x = U.symm (T (U x)) := rfl

@[simp] theorem conjugate_smul (U : E ≃ₗᵢ[ℂ] F) (c : ℂ) (T : F →L[ℂ] F) :
    conjugate U (c • T) = c • conjugate U T := by ext x; simp

theorem conjugate_symmetric (U : E ≃ₗᵢ[ℂ] F) (T : F →L[ℂ] F)
    (hT : T.toLinearMap.IsSymmetric) : (conjugate U T).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℂ (U.symm (T (U x))) y = inner ℂ x (U.symm (T (U y)))
  rw [← U.inner_map_map, ← U.inner_map_map x]
  simpa using hT (U x) (U y)

/-- Orthogonal kernel projections commute with unitary change of coordinates. -/
theorem conjugate_kernel_projection [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (U : E ≃ₗᵢ[ℂ] F) (T : F →L[ℂ] F) :
    conjugate U (LinearMap.ker T.toLinearMap).starProjection =
      (LinearMap.ker (conjugate U T).toLinearMap).starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · change U.symm (T (U (U.symm ((LinearMap.ker T.toLinearMap).starProjection (U x))))) = 0
    simp only [U.apply_symm_apply]
    have hmem := (LinearMap.ker T.toLinearMap).starProjection_apply_mem (U x)
    change T ((LinearMap.ker T.toLinearMap).starProjection (U x)) = 0 at hmem
    simp [hmem]
  · intro w hw
    change U.symm (T (U w)) = 0 at hw
    have hw' : U w ∈ LinearMap.ker T.toLinearMap := by
      change T (U w) = 0
      exact U.symm.injective (by simpa using hw)
    rw [← U.inner_map_map]
    simp only [map_sub, conjugate_apply, U.apply_symm_apply]
    exact (LinearMap.ker T.toLinearMap).starProjection_inner_eq_zero (U x) (U w) hw'
end Conjugation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
variable {ι : Type*} [Fintype ι]

/-- Coordinatewise diagonalization gives equality of the actual bounded operators. -/
theorem operator_eq_conjugate (U : E ≃ₗᵢ[ℂ] Vec ι) (A : E →L[ℂ] E)
    (a : ι → ℝ) (hdiag : ∀ x i, U (A x) i = (a i : ℂ) * U x i) :
    A = conjugate U (diagonal (fun i => (a i : ℂ))) := by
  apply ContinuousLinearMap.ext
  intro x
  apply U.injective
  ext i
  simpa using hdiag x i

theorem blockAuxiliary_eq_conjugate (U : E ≃ₗᵢ[ℂ] Vec ι) (A : E →L[ℂ] E)
    (a : ι → ℝ) (hdiag : ∀ x i, U (A x) i = (a i : ℂ) * U x i) (t : ℝ) :
    blockAuxiliary A t = conjugate (tripleCoordinates U) (auxiliary a t) := by
  apply ContinuousLinearMap.ext
  intro x
  apply (tripleCoordinates U).injective
  simpa using tripleCoordinates_intertwines U A a hdiag t x

/-- Exact identification of the original-coordinate kernel projection. -/
theorem original_kernel_projection (U : E ≃ₗᵢ[ℂ] Vec ι) (A : E →L[ℂ] E)
    (a : ι → ℝ) (hdiag : ∀ x i, U (A x) i = (a i : ℂ) * U x i)
    {t : ℝ} (ht : 0 < t) :
    (LinearMap.ker (blockAuxiliary A t).toLinearMap).starProjection =
      conjugate (tripleCoordinates U) (kernelProjector a t) := by
  rw [blockAuxiliary_eq_conjugate U A a hdiag, kernelProjector_eq_orthogonalProjection a ht,
    conjugate_kernel_projection]

/-- All four defining Moore–Penrose equations, in the original coordinates. -/
theorem original_moore_penrose (U : E ≃ₗᵢ[ℂ] Vec ι) (A : E →L[ℂ] E)
    (a : ι → ℝ) (hdiag : ∀ x i, U (A x) i = (a i : ℂ) * U x i)
    {t : ℝ} (ht : 0 < t) :
    let H := blockAuxiliary A t
    let Q := conjugate (tripleCoordinates U) (pseudoInverse a t)
    H * Q * H = H ∧ Q * H * Q = Q ∧
      (H * Q).toLinearMap.IsSymmetric ∧ (Q * H).toLinearMap.IsSymmetric := by
  dsimp only
  rw [blockAuxiliary_eq_conjugate U A a hdiag]
  simp only [← map_mul]
  have href := moore_penrose_reflexive a ht
  rw [href.1, href.2, auxiliary_mul_pseudoInverse a ht, pseudoInverse_mul_auxiliary a ht]
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> apply conjugate_symmetric
  all_goals
    rw [kernelProjector_eq_orthogonalProjection a ht]
    exact LinearMap.IsSymmetric.id.sub (LinearMap.ker (auxiliary a t).toLinearMap).starProjection_isSymmetric

end OptimalQLS.Geometry
