import OptimalQLS.Geometry.Resolvent

noncomputable section
namespace OptimalQLS.Geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Proposition 5.3, exact operator identity for any finite-dimensional
Hermitian input satisfying the paper's operator-norm promises. -/
theorem proposition53_identity (A : E →L[ℂ] E) (hA : A.toLinearMap.IsSymmetric)
    (hunit : IsUnit A) {κ : ℝ} (hκ : 0 < κ)
    (hAnorm : ‖A‖ ≤ 1) (hinorm : ‖Ring.inverse A‖ ≤ κ) :
    ((1 : E →L[ℂ] E) + ((κ⁻¹)^2 : ℂ) • (Ring.inverse A)^2) * A *
      Ring.inverse (A^2 + ((κ⁻¹)^2 : ℂ) • (1 : E →L[ℂ] E)) = Ring.inverse A := by
  let U := (hA.eigenvectorBasis rfl).repr
  let a := hA.eigenvalues rfl
  have hdiag : ∀ x i, U (A x) i = (a i : ℂ) * U x i :=
    fun x i => hA.eigenvectorBasis_apply_self_apply rfl x i
  have ha : ∀ i, a i ≠ 0 := by
    intro i hi
    have h := (spectral_coordinate_bounds A hA hunit hκ hAnorm hinorm i).1
    change κ⁻¹ ≤ |a i| at h
    rw [hi, abs_zero] at h
    exact (not_le_of_gt (inv_pos.mpr hκ)) h
  have hinv := (inverse_from_coordinates U A a hdiag ha).2
  have hres := (resolvent_inverse U A a hdiag (inv_pos.mpr hκ)).2
  have hc : 1 + ((κ⁻¹)^2 : ℂ) • (Ring.inverse A)^2 =
      conjugate U (diagonal (fun i => ((1 + (κ⁻¹)^2 / a i ^ 2 : ℝ) : ℂ))) := by
    rw [correction_operator_formula, map_add, map_one, conjugate_smul, map_pow, ← hinv]
  rw [hc, hres, hinv, operator_eq_conjugate U A a hdiag, ← map_mul, ← map_mul,
    correction_operator_identity a (inv_pos.mpr hκ) ha]
  simp

/-- Proposition 5.3, both Loewner inequalities, expressed as quadratic
forms on the original Hilbert space. -/
theorem proposition53_order (A : E →L[ℂ] E) (hA : A.toLinearMap.IsSymmetric)
    (hunit : IsUnit A) {κ : ℝ} (hκ : 0 < κ)
    (hAnorm : ‖A‖ ≤ 1) (hinorm : ‖Ring.inverse A‖ ≤ κ) (x : E) :
    ‖x‖ ^ 2 ≤ (inner ℂ x (((1 : E →L[ℂ] E) + ((κ⁻¹)^2 : ℂ) • (Ring.inverse A)^2) x)).re ∧
    (inner ℂ x (((1 : E →L[ℂ] E) + ((κ⁻¹)^2 : ℂ) • (Ring.inverse A)^2) x)).re ≤ 2 * ‖x‖ ^ 2 := by
  let U := (hA.eigenvectorBasis rfl).repr
  let a := hA.eigenvalues rfl
  have hdiag : ∀ x i, U (A x) i = (a i : ℂ) * U x i :=
    fun x i => hA.eigenvectorBasis_apply_self_apply rfl x i
  have ha : ∀ i, κ⁻¹ ≤ |a i| := fun i =>
    (spectral_coordinate_bounds A hA hunit hκ hAnorm hinorm i).1
  have hane : ∀ i, a i ≠ 0 := by
    intro i hi
    have h := ha i
    rw [hi, abs_zero] at h
    exact (not_le_of_gt (inv_pos.mpr hκ)) h
  have hinv := (inverse_from_coordinates U A a hdiag hane).2
  have hc : 1 + ((κ⁻¹)^2 : ℂ) • (Ring.inverse A)^2 =
      conjugate U (diagonal (fun i => ((1 + (κ⁻¹)^2 / a i ^ 2 : ℝ) : ℂ))) := by
    rw [correction_operator_formula, map_add, map_one, conjugate_smul, map_pow, ← hinv]
  rw [hc]
  have hinner : inner ℂ x (conjugate U
      (diagonal (fun i => ((1 + (κ⁻¹)^2 / a i ^ 2 : ℝ) : ℂ))) x) =
      inner ℂ (U x) (diagonal (fun i => ((1 + (κ⁻¹)^2 / a i ^ 2 : ℝ) : ℂ)) (U x)) := by
    rw [← U.inner_map_map]
    simp
  rw [hinner]
  have h := correction_operator_bounds a (inv_pos.mpr hκ) ha
  have hl := h.1 (U x)
  have hu := h.2 (U x)
  have hn : (inner ℂ (U x) (U x)).re = ‖x‖ ^ 2 := by
    change RCLike.re (inner ℂ (U x) (U x)) = ‖x‖ ^ 2
    rw [← norm_sq_eq_re_inner, U.norm_map]
  simp only [ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    two_smul, inner_add_right, Complex.add_re, hn] at hl hu
  exact ⟨hl, by linarith⟩

/-- Inversion preserves Hermiticity for an invertible bounded operator. -/
theorem inverse_symmetric (A : E →L[ℂ] E) (hA : A.toLinearMap.IsSymmetric)
    (hunit : IsUnit A) : (Ring.inverse A).toLinearMap.IsSymmetric := by
  intro x y
  calc
    inner ℂ (Ring.inverse A x) y = inner ℂ (Ring.inverse A x) (A (Ring.inverse A y)) := by
      rw [OptimalQLS.Perturbation.apply_inverse A hunit]
    _ = inner ℂ (A (Ring.inverse A x)) (Ring.inverse A y) := (hA _ _).symm
    _ = inner ℂ x (Ring.inverse A y) := by rw [OptimalQLS.Perturbation.apply_inverse A hunit]

/-- The operator compared in Proposition 5.3 is itself Hermitian, so the
quadratic-form inequalities are literal Loewner-order inequalities. -/
theorem correction_symmetric (A : E →L[ℂ] E) (hA : A.toLinearMap.IsSymmetric)
    (hunit : IsUnit A) (t : ℝ) :
    ((1 : E →L[ℂ] E) + (t ^ 2 : ℂ) • (Ring.inverse A)^2).toLinearMap.IsSymmetric := by
  change (LinearMap.id + (t ^ 2 : ℂ) • (Ring.inverse A).toLinearMap ^ 2).IsSymmetric
  exact LinearMap.IsSymmetric.id.add (LinearMap.IsSymmetric.smul (by simp)
    ((inverse_symmetric A hA hunit).pow 2))

end OptimalQLS.Geometry
