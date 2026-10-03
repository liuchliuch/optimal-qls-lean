import OptimalQLS.PolynomialTransform.Spectral
import OptimalQLS.Geometry.Lemma42

/-! # Lemma 5.2: the explicit polynomial on the actual normalized graph operator -/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

def graphNormalization (κ : ℝ) : ℝ := 1 + κ⁻¹

def graphFilterGap (κ : ℝ) : ℝ :=
  min (1 / (κ * graphNormalization κ)) (1 / Real.sqrt 12)

def normalizedAuxiliary (A : E →L[ℂ] E) (κ : ℝ) : Block E →L[ℂ] Block E :=
  ((graphNormalization κ)⁻¹ : ℂ) • blockAuxiliary A κ⁻¹

theorem graphNormalization_pos {κ : ℝ} (hκ : 0 < κ) : 0 < graphNormalization κ := by
  unfold graphNormalization
  positivity

theorem graphFilterGap_pos {κ : ℝ} (hκ : 0 < κ) : 0 < graphFilterGap κ := by
  unfold graphFilterGap
  exact lt_min (by positivity [graphNormalization_pos hκ]) (by positivity)

/-- The analytic register-block operator bound from Lemma 5.2, with no
extra spectral-gap hypothesis and the actual graph-kernel projection. -/
theorem lemma52_filter_operator (A : E →L[ℂ] E) (hA : A.toLinearMap.IsSymmetric)
    (hunit : IsUnit A) {κ η : ℝ} (hκ : 0 < κ)
    (hAnorm : ‖A‖ ≤ 1) (hinorm : ‖Ring.inverse A‖ ≤ κ)
    (hη0 : 0 < η) (hη1 : η < 1 / 2) :
    ‖polynomialOperator (kernelFilter (graphFilterGap κ) η) (normalizedAuxiliary A κ) -
      (LinearMap.ker (blockAuxiliary A κ⁻¹).toLinearMap).starProjection‖ ≤ η := by
  let H := blockAuxiliary A κ⁻¹
  have hH : H.toLinearMap.IsSymmetric := lemma42_auxiliary_hermitian A hA κ⁻¹
  let U := (hH.eigenvectorBasis rfl).repr
  let a := hH.eigenvalues rfl
  let α := graphNormalization κ
  have hα : 0 < α := graphNormalization_pos hκ
  have hdiag : ∀ x i, U (H x) i = (a i : ℂ) * U x i :=
    fun x i => hH.eigenvectorBasis_apply_self_apply rfl x i
  have hncoords : ∀ x i, U (normalizedAuxiliary A κ x) i =
      ((a i / α : ℝ) : ℂ) * U x i := by
    intro x i
    simp only [normalizedAuxiliary, ContinuousLinearMap.smul_apply, map_smul,
      PiLp.smul_apply, smul_eq_mul]
    change (α : ℂ)⁻¹ * U (H x) i = _
    rw [hdiag]
    push_cast
    ring
  rw [kernel_projection_coordinates U H a hdiag]
  apply polynomial_diagonal_distance U (normalizedAuxiliary A κ)
    (fun i => a i / α) hncoords _ (zeroIndicator a) hη0.le
  intro i
  by_cases hai : a i = 0
  · have hp0 := (lemma51_kernel_filter (graphFilterGap_pos hκ)
        (min_le_right _ _) hη0 hη1).2.2.1
    simp [zeroIndicator, hai, hp0, hη0.le]
  · have hainz : (a i : ℂ) ≠ 0 := by exact_mod_cast hai
    have heig := Module.End.hasEigenvalue_of_hasEigenvector
      (hH.hasEigenvector_eigenvectorBasis rfl i)
    have hgap := lemma42_spectral_gap A hA hunit hκ hAnorm hinorm hainz heig
    have hgap' : Real.sqrt 2 / κ ≤ |a i| ∧ |a i| ≤ Real.sqrt (1 + (κ⁻¹)^2) := by
      simpa [Complex.norm_real, Real.norm_eq_abs] using hgap
    have hlow : graphFilterGap κ ≤ |a i / α| := by
      rw [abs_div, abs_of_pos hα]
      apply (min_le_left _ _).trans
      apply (le_div_iff₀ hα).mpr
      have hs : (1 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
      have hone : κ⁻¹ ≤ |a i| := by
        calc
          κ⁻¹ = 1 / κ := inv_eq_one_div _
          _ ≤ Real.sqrt 2 / κ := div_le_div_of_nonneg_right hs hκ.le
          _ ≤ |a i| := hgap'.1
      convert hone using 1
      dsimp only [α]
      field_simp [ne_of_gt (graphNormalization_pos hκ)]
    have hupp : |a i / α| ≤ 1 := by
      rw [abs_div, abs_of_pos hα, div_le_one hα]
      apply hgap'.2.trans
      apply (Real.sqrt_le_left hα.le).mpr
      dsimp only [α, graphNormalization]
      have ht : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ.le
      nlinarith
    simpa [zeroIndicator, hai] using
      kernelFilter_tail (graphFilterGap_pos hκ) (min_le_right _ _) hη0 hlow hupp

/-- The paper's graph gap is never smaller than 1/(4κ). -/
theorem graphFilterGap_inverse_bound {κ : ℝ} (hκ : 1 ≤ κ) :
    (graphFilterGap κ)⁻¹ ≤ 4 * κ := by
  have hk : 0 < κ := by linarith
  have hα : 0 < graphNormalization κ := graphNormalization_pos hk
  have hκα : κ * graphNormalization κ ≤ 4 * κ := by
    unfold graphNormalization
    rw [mul_add, mul_one, mul_inv_cancel₀ hk.ne']
    linarith
  have hs : Real.sqrt 12 ≤ 4 * κ := by
    have hs4 : Real.sqrt 12 ≤ (4 : ℝ) := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
    linarith
  have hlo : 1 / (4 * κ) ≤ graphFilterGap κ := by
    apply le_min
    · exact one_div_le_one_div_of_le (mul_pos hk hα) hκα
    · exact one_div_le_one_div_of_le (Real.sqrt_pos.2 (by norm_num)) hs
  have hi := inv_le_inv₀ (graphFilterGap_pos hk) (by positivity : 0 < 1 / (4 * κ))
  have hh := hi.mpr hlo
  simpa using hh

/-- Explicit O(κ log(1/η)) degree constant for the actual graph filter. -/
theorem graphFilter_degree_bound {κ η : ℝ} (hκ : 1 ≤ κ) (hη0 : 0 < η)
    (hη1 : η < 1 / 2) :
    ((kernelFilter (graphFilterGap κ) η).natDegree : ℝ) < 24 * κ * Real.log (1 / η) := by
  have hk : 0 < κ := by linarith
  have hlog : 0 ≤ Real.log (1 / η) := Real.log_nonneg
    ((le_div_iff₀ hη0).mpr (by linarith))
  apply (kernelFilter_degree_complexity (graphFilterGap_pos hk) (min_le_right _ _)
    hη0 hη1).trans_le
  have hm := mul_le_mul_of_nonneg_right (graphFilterGap_inverse_bound hκ) hlog
  nlinarith

end OptimalQLS.PolynomialTransform
