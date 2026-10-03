import OptimalQLS.PolynomialTransform.GraphKernel

/-! # Sharper resource bounds for the paper's exact graph-filter parameter -/
noncomputable section
namespace OptimalQLS.PolynomialTransform

theorem graphFilterGap_inverse_bound_two {κ : ℝ} (hκ : 2 ≤ κ) :
    (graphFilterGap κ)⁻¹ ≤ 2*κ := by
  have hk : 0 < κ := by linarith
  have hα : 0 < graphNormalization κ := graphNormalization_pos hk
  have hprod : κ*graphNormalization κ ≤ 2*κ := by
    unfold graphNormalization
    rw [mul_add,mul_one,mul_inv_cancel₀ hk.ne']
    linarith
  have hroot : Real.sqrt 12 ≤ 2*κ := by
    have hs : Real.sqrt 12 ≤ 4 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
    linarith
  have hlo : 1/(2*κ) ≤ graphFilterGap κ := by
    apply le_min
    · exact one_div_le_one_div_of_le (mul_pos hk hα) hprod
    · exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num)) hroot
  have hi := (inv_le_inv₀ (graphFilterGap_pos hk) (by positivity : 0 < 1/(2*κ))).mpr hlo
  simpa using hi

theorem paperGraphFilter_degree_bound {κ η : ℝ} (hκ : 2 ≤ κ) (hη0 : 0 < η) (hη1 : η < 1/2) :
    ((kernelFilter (graphFilterGap κ) η).natDegree : ℝ) < 12*κ*Real.log (1/η) := by
  have hk : 0 < κ := by linarith
  have hl : 0 ≤ Real.log (1/η) := Real.log_nonneg ((le_div_iff₀ hη0).mpr (by linarith))
  have hd := kernelFilter_degree_complexity (graphFilterGap_pos hk) (min_le_right _ _) hη0 hη1
  have hm := mul_le_mul_of_nonneg_right (graphFilterGap_inverse_bound_two hκ) hl
  nlinarith

end OptimalQLS.PolynomialTransform
