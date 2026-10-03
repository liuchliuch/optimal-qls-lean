import OptimalQLS.LowerBounds.HistoryInverse

/-!
# Quantitative operator norm estimates for the concrete cyclic resolvent

The geometric inverse is bounded in the genuine Euclidean operator norm.
These are matrix-norm statements, rather than abstract norm certificates.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds

lemma real_geometric_sum (lam : ℝ) (N : ℕ) (hne : lam ≠ 1) :
    (∑ k ∈ Finset.range N, lam ^ k) = (1 - lam ^ N) / (1 - lam) := by
  apply (eq_div_iff (sub_ne_zero.mpr (Ne.symm hne))).mpr
  exact geom_sum_mul_neg lam N

/-- Norm at most one for the actual history matrix. -/
theorem historyMatrix_norm_le_one {N : ℕ} [NeZero N] (profile : Fin N → Bool)
    (lam : ℝ) (h0 : 0 ≤ lam) :
    ‖historyMatrix profile (lam : ℂ)‖ ≤ 1 := by
  have hp : 0 < 1 + lam := by linarith
  have hn : ‖(1 : ℂ) + (lam : ℂ)‖ = 1 + lam := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real, Real.norm_of_nonneg hp.le]
  have hb : ‖(lam : ℂ) • historyStep profile‖ = lam := by
    simp [norm_smul, historyStep_norm, Complex.norm_real, Real.norm_of_nonneg h0]
  rw [historyMatrix, norm_smul, norm_inv, hn]
  calc
    (1 + lam)⁻¹ * ‖1 - (lam : ℂ) • historyStep profile‖
        ≤ (1 + lam)⁻¹ * (1 + lam) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hp.le)
      calc
        _ ≤ ‖(1 : Matrix (HistoryBasis N) (HistoryBasis N) ℂ)‖ +
            ‖(lam : ℂ) • historyStep profile‖ := norm_sub_le _ _
        _ = 1 + lam := by rw [norm_one, hb]
    _ = 1 := inv_mul_cancel₀ hp.ne'

/-- Exact-period finite sum gives the sharp inverse upper bound. -/
theorem cyclicHistoryInverse_norm_le {N : ℕ} [NeZero N] (profile : Fin N → Bool)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam < 1) :
    ‖cyclicInverse (historyStep profile) (lam : ℂ) N‖ ≤ (1 - lam)⁻¹ := by
  have hpow : lam ^ N < 1 := pow_lt_one₀ h0 h1 (NeZero.ne N)
  have hp : 0 < 1 - lam ^ N := by linarith
  have hd : ‖(1 : ℂ) - (lam : ℂ) ^ N‖ = 1 - lam ^ N := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_of_nonneg hp.le]
  have hb : ‖(lam : ℂ) • historyStep profile‖ = lam := by
    simp [norm_smul, historyStep_norm, Complex.norm_real, Real.norm_of_nonneg h0]
  rw [cyclicInverse, norm_smul, norm_inv, hd]
  calc
    (1 - lam ^ N)⁻¹ * ‖∑ k ∈ Finset.range N, ((lam : ℂ) • historyStep profile) ^ k‖
        ≤ (1 - lam ^ N)⁻¹ * (∑ k ∈ Finset.range N, lam ^ k) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hp.le)
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      calc
        _ ≤ ‖(lam : ℂ) • historyStep profile‖ ^ k := norm_pow_le _ k
        _ = lam ^ k := by rw [hb]
    _ = (1 - lam)⁻¹ := by
      rw [real_geometric_sum lam N h1.ne]
      field_simp

/-- Sharp normalized inverse upper bound `(1+lam)/(1-lam)`. -/
theorem historyInverse_norm_le {N : ℕ} [NeZero N] (profile : Fin N → Bool)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam < 1) :
    ‖historyInverse profile (lam : ℂ)‖ ≤ (1 + lam) / (1 - lam) := by
  have hp : 0 ≤ 1 + lam := by linarith
  have hn : ‖(1 : ℂ) + (lam : ℂ)‖ = 1 + lam := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real, Real.norm_of_nonneg hp]
  rw [historyInverse, norm_smul, hn, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (cyclicHistoryInverse_norm_le profile lam h0 h1) hp

end OptimalQLS.LowerBounds
