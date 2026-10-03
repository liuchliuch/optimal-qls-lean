import OptimalQLS.Geometry.OriginalCoordinates

noncomputable section
namespace OptimalQLS.Geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
variable {ι : Type*} [Fintype ι]

/-- Invertibility follows from nonvanishing spectral coordinates. -/
theorem inverse_from_coordinates (U : E ≃ₗᵢ[ℂ] Vec ι) (A : E →L[ℂ] E)
    (a : ι → ℝ) (hdiag : ∀ x i, U (A x) i = (a i : ℂ) * U x i)
    (ha : ∀ i, a i ≠ 0) :
    IsUnit A ∧ Ring.inverse A = conjugate U (diagonal (fun i => ((a i)⁻¹ : ℂ))) := by
  let R := conjugate U (diagonal (fun i => ((a i)⁻¹ : ℂ)))
  have hAR : A * R = 1 := by
    rw [operator_eq_conjugate U A a hdiag]
    change conjugate U _ * conjugate U _ = 1
    rw [← map_mul]
    have h : diagonal (fun i => (a i : ℂ)) * diagonal (fun i => ((a i)⁻¹ : ℂ)) = 1 := by
      ext x i
      have hi : (a i : ℂ) ≠ 0 := by exact_mod_cast ha i
      simp [ContinuousLinearMap.mul_apply, ← mul_assoc, hi]
    rw [h, map_one]
  have hRA : R * A = 1 := by
    rw [operator_eq_conjugate U A a hdiag]
    change conjugate U _ * conjugate U _ = 1
    rw [← map_mul]
    have h : diagonal (fun i => ((a i)⁻¹ : ℂ)) * diagonal (fun i => (a i : ℂ)) = 1 := by
      ext x i
      have hi : (a i : ℂ) ≠ 0 := by exact_mod_cast ha i
      simp [ContinuousLinearMap.mul_apply, ← mul_assoc, hi]
    rw [h, map_one]
  have hu : IsUnit A := ⟨⟨A, R, hAR, hRA⟩, rfl⟩
  refine ⟨hu, ?_⟩
  change Ring.inverse A = R
  calc
    Ring.inverse A = Ring.inverse A * (A * R) := by rw [hAR, mul_one]
    _ = R := by rw [← mul_assoc, Ring.inverse_mul_cancel A hu, one_mul]

/-- The squared shifted operator is diagonalized in the same basis. -/
theorem resolvent_coordinates (U : E ≃ₗᵢ[ℂ] Vec ι) (A : E →L[ℂ] E)
    (a : ι → ℝ) (hdiag : ∀ x i, U (A x) i = (a i : ℂ) * U x i) (t : ℝ)
    (x : E) (i : ι) :
    U ((A ^ 2 + (t ^ 2 : ℂ) • (1 : E →L[ℂ] E)) x) i =
      ((a i ^ 2 + t ^ 2 : ℝ) : ℂ) * U x i := by
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, pow_two, ContinuousLinearMap.mul_apply,
    map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hdiag]
  push_cast
  ring

/-- D⁻¹ is derived as the actual ring inverse of D=A²+t²I. -/
theorem resolvent_inverse (U : E ≃ₗᵢ[ℂ] Vec ι) (A : E →L[ℂ] E)
    (a : ι → ℝ) (hdiag : ∀ x i, U (A x) i = (a i : ℂ) * U x i)
    {t : ℝ} (ht : 0 < t) :
    IsUnit (A ^ 2 + (t ^ 2 : ℂ) • (1 : E →L[ℂ] E)) ∧
    Ring.inverse (A ^ 2 + (t ^ 2 : ℂ) • (1 : E →L[ℂ] E)) =
      conjugate U (diagonal (fun i => (((a i ^ 2 + t ^ 2)⁻¹ : ℝ) : ℂ))) := by
  simpa only [Complex.ofReal_inv] using
    inverse_from_coordinates U (A ^ 2 + (t ^ 2 : ℂ) • (1 : E →L[ℂ] E))
      (fun i => a i ^ 2 + t ^ 2) (resolvent_coordinates U A a hdiag t)
      (fun i => ne_of_gt (denominator_pos (a := a i) ht))

/-- Exact input projection formula in arbitrary original coordinates. -/
theorem original_projection_input (U : E ≃ₗᵢ[ℂ] Vec ι) (A : E →L[ℂ] E)
    (a : ι → ℝ) (hdiag : ∀ x i, U (A x) i = (a i : ℂ) * U x i)
    {t : ℝ} (ht : 0 < t) (b : E) :
    (LinearMap.ker (blockAuxiliary A t).toLinearMap).starProjection (blockTriple 0 b 0) =
      blockTriple 0 ((t ^ 2 : ℂ) • (Ring.inverse (A ^ 2 + (t ^ 2 : ℂ) • (1 : E →L[ℂ] E)) b))
        ((t : ℂ) • A (Ring.inverse (A ^ 2 + (t ^ 2 : ℂ) • (1 : E →L[ℂ] E)) b)) := by
  rw [original_kernel_projection U A a hdiag ht, (resolvent_inverse U A a hdiag ht).2]
  apply (tripleCoordinates U).injective
  simp only [conjugate_apply, LinearIsometryEquiv.apply_symm_apply,
    tripleCoordinates_blockTriple, map_zero, kernelProjector_input]
  have hreal (r : ℝ) (v : E) (i : ι) : U (r • v) i = (r : ℂ) * U v i := by
    simpa using congrArg (fun w : Vec ι => w i) (U.map_smul (r : ℂ) v)
  ext ⟨j,i⟩
  fin_cases j <;> simp [triple, hreal, hdiag, map_smul]
  all_goals
    push_cast
    simp only [div_eq_mul_inv]
    ring

/-- Exact pseudoinverse formula in arbitrary original coordinates. -/
theorem original_pseudoInverse_input (U : E ≃ₗᵢ[ℂ] Vec ι) (A : E →L[ℂ] E)
    (a : ι → ℝ) (hdiag : ∀ x i, U (A x) i = (a i : ℂ) * U x i)
    {t : ℝ} (ht : 0 < t) (b : E) :
    conjugate (tripleCoordinates U) (pseudoInverse a t) (blockTriple 0 b 0) =
      blockTriple (A (Ring.inverse (A ^ 2 + (t ^ 2 : ℂ) • (1 : E →L[ℂ] E)) b)) 0 0 := by
  rw [(resolvent_inverse U A a hdiag ht).2]
  apply (tripleCoordinates U).injective
  simp only [conjugate_apply, LinearIsometryEquiv.apply_symm_apply,
    tripleCoordinates_blockTriple, map_zero, pseudoInverse_input]
  have hreal (r : ℝ) (v : E) (i : ι) : U (r • v) i = (r : ℂ) * U v i := by
    simpa using congrArg (fun w : Vec ι => w i) (U.map_smul (r : ℂ) v)
  ext ⟨j,i⟩
  fin_cases j <;> simp [triple, hreal, hdiag, map_smul]
  push_cast
  simp only [div_eq_mul_inv]
  ring

end OptimalQLS.Geometry
