import OptimalQLS.LowerBounds.HistorySourceProfile

/-! Explicit constant1/256 in the parity-tail probability calculation. -/
noncomputable section
open scoped BigOperators
namespace OptimalQLS.LowerBounds

theorem historyLambda_square_gap_bound {kappa : ℝ} (hk : 4 ≤ kappa) :
    1 - historyLambda kappa ^ 2 ≤ 4 / kappa := by
  have h0 := historyLambda_nonneg hk
  have h1 := historyLambda_lt_one hk
  have hg : 0 ≤ 1 - historyLambda kappa := by linarith
  calc
    1 - historyLambda kappa ^ 2 =
        (1 - historyLambda kappa) * (1 + historyLambda kappa) := by ring
    _ ≤ (1 - historyLambda kappa) * 2 := mul_le_mul_of_nonneg_left (by linarith) hg
    _ = 4 / (kappa + 1) := by rw [historyLambda_gap hk]; ring
    _ ≤ 4 / kappa := by
      apply (div_le_div_iff₀ (by linarith : 0 < kappa + 1) (by linarith : 0 < kappa)).mpr
      linarith

theorem historyPadding_square_gap_bound {kappa : ℝ} (hk : 4 ≤ kappa) :
    (historyPadding kappa : ℝ) * (1 - historyLambda kappa ^ 2) ≤ 36 := by
  have h0 := historyLambda_nonneg hk
  have h1 := historyLambda_lt_one hk
  have hg : 0 ≤ 1 - historyLambda kappa ^ 2 := by nlinarith
  calc
    _ ≤ (9 * kappa) * (4 / kappa) :=
      mul_le_mul (historyPadding_upper hk) (historyLambda_square_gap_bound hk) hg (by linarith)
    _ = 36 := by field_simp; ring

/-- A fully quantified numerical tail coefficient, independent of any matrix
or probability assumptions. -/
theorem geometric_tail_coefficient_lower (lam : ℝ) (ell : ℕ) (hell : 0 < ell)
    (h0 : 0 ≤ lam) (h1 : lam < 1) (hdecay : lam ^ ell ≤ 1 / 2)
    (hscale : (ell : ℝ) * (1 - lam ^ 2) ≤ 36) :
    (1 / 256 : ℝ) ≤ ((1 - lam ^ ell) ^ 2 / (ell : ℝ)) *
      (∑ k : Fin ell, (lam ^ 2) ^ k.val) := by
  have he : (0 : ℝ) < ell := by exact_mod_cast hell
  have hg : 0 < 1 - lam ^ 2 := by nlinarith
  have hu : 0 ≤ lam ^ ell := pow_nonneg h0 ell
  have ha : (1 / 4 : ℝ) ≤ (1 - lam ^ ell) ^ 2 := by nlinarith
  have hb : (3 / 4 : ℝ) ≤ 1 - (lam ^ ell) ^ 2 := by nlinarith
  have hab : (3 / 16 : ℝ) ≤ (1 - lam ^ ell) ^ 2 * (1 - (lam ^ ell) ^ 2) := by
    have h := mul_le_mul ha hb (by norm_num : (0 : ℝ) ≤ 3 / 4) (sq_nonneg (1 - lam ^ ell))
    norm_num at h ⊢
    linarith
  rw [Fin.sum_univ_eq_sum_range, real_geometric_sum (lam ^ 2) ell (by linarith)]
  have hpow : (lam ^ 2) ^ ell = (lam ^ ell) ^ 2 := by simp [← pow_mul, Nat.mul_comm]
  rw [hpow]
  have heq : (1 - lam ^ ell) ^ 2 / (ell : ℝ) *
      ((1 - (lam ^ ell) ^ 2) / (1 - lam ^ 2)) =
      ((1 - lam ^ ell) ^ 2 * (1 - (lam ^ ell) ^ 2)) /
        ((ell : ℝ) * (1 - lam ^ 2)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq]
  apply (le_div_iff₀ (mul_pos he hg)).mpr
  nlinarith

theorem history_tail_coefficient_lower {kappa : ℝ} (hk : 4 ≤ kappa) :
    (1 / 256 : ℝ) ≤ ((1 - historyLambda kappa ^ historyPadding kappa) ^ 2 /
      (historyPadding kappa : ℝ)) *
      (∑ k : Fin (historyPadding kappa), (historyLambda kappa ^ 2) ^ k.val) :=
  geometric_tail_coefficient_lower _ _ (historyPadding_pos hk) (historyLambda_nonneg hk)
    (historyLambda_lt_one hk) (historyLambda_pow_padding_le_half hk)
    (historyPadding_square_gap_bound hk)

end OptimalQLS.LowerBounds
