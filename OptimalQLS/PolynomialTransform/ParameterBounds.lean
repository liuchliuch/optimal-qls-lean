import OptimalQLS.PolynomialTransform.ChebyshevFilter

/-! # Explicit scalar constants for the paper's resource bounds -/
noncomputable section
namespace OptimalQLS.PolynomialTransform

theorem kappa_log_ge_one {κ η : ℝ} (hκ : 2 ≤ κ) (hη0 : 0 < η) (hη1 : η < 1/2) :
    1 ≤ κ*Real.log (1/η) := by
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
  rw [Real.log_inv] at hl
  norm_num at hl
  have htwo : (2 : ℝ) ≤ 1/η := (le_div_iff₀ hη0).mpr (by linarith)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) htwo
  have hk : 0 ≤ κ := by linarith
  have hm := mul_le_mul_of_nonneg_left (show (1/2 : ℝ) ≤ Real.log (1/η) by linarith) hk
  nlinarith

theorem graph_gate_bound_linear (a : ℕ) {κ η : ℝ}
    (hκ : 2 ≤ κ) (hη0 : 0 < η) (hη1 : η < 1/2) :
    (6248*(a+5)+977056)*(12*κ*Real.log (1/η)+1) ≤
      13107848*κ*(a+1)*Real.log (1/η) := by
  have hm := kappa_log_ge_one hκ hη0 hη1
  have ha : 6248*((a : ℝ)+5)+977056 ≤ 1008296*(a+1) := by nlinarith [Nat.cast_nonneg (α := ℝ) a]
  have hb : 12*κ*Real.log (1/η)+1 ≤ 13*(κ*Real.log (1/η)) := by nlinarith
  calc
    _ ≤ (1008296*(a+1))*(13*(κ*Real.log (1/η))) :=
      mul_le_mul ha hb (by nlinarith) (by positivity)
    _ = _ := by ring

theorem correction_gate_bound_linear (a : ℕ) {κ η : ℝ}
    (hκ : 2 ≤ κ) (hη0 : 0 < η) (hη1 : η < 1/2) :
    6248*(210000*κ*Real.log (1/η)+1)*(a+1) ≤
      1312086248*κ*(a+1)*Real.log (1/η) := by
  have hm := kappa_log_ge_one hκ hη0 hη1
  have h : 210000*κ*Real.log (1/η)+1 ≤ 210001*(κ*Real.log (1/η)) := by nlinarith
  calc
    _ ≤ 6248*(210001*(κ*Real.log (1/η)))*(a+1) := by gcongr
    _ = _ := by ring

end OptimalQLS.PolynomialTransform
