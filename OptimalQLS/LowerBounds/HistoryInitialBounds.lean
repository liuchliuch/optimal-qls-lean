import OptimalQLS.LowerBounds.HistoryAmplitudeBounds

/-! Quantitative lower bounds on amplitudes inside the padded source interval. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Fin.NatCast
namespace OptimalQLS.LowerBounds
open Matrix

lemma history_initial_partial_sum {N ell : ℕ} [NeZero N] (hN : ell ≤ N)
    (lam : ℝ) (h0 : 0 ≤ lam) (j : Fin N) (hj : j.val < ell) :
    (∑ i : Fin (j.val + 1), lam ^ i.val) ≤
      ∑ i : Fin ell, lam ^ (j - (i.val : Fin N)).val := by
  have hcast : ∀ i : Fin (j.val + 1), (i.val : Fin N).val = i.val := by
    intro i
    exact Fin.val_cast_of_lt (by omega)
  have hgeom : (∑ i : Fin (j.val + 1), lam ^ (j - (i.val : Fin N)).val) =
      ∑ i : Fin (j.val + 1), lam ^ i.val := by
    calc
      _ = ∑ i : Fin (j.val + 1), lam ^ ((j.val + 1) - 1 - i.val) := by
        apply Finset.sum_congr rfl
        intro i _
        have hle : (i.val : Fin N) ≤ j := by
          apply Fin.le_iff_val_le_val.mpr
          rw [hcast]
          omega
        rw [Fin.sub_val_of_le hle, hcast]
        simp
      _ = _ := sum_reverse_powers _ _
  rw [← hgeom, ← sum_fin_initial_segment ell (j.val + 1) (by omega)
    (fun t : ℕ => lam ^ (j - (t : Fin N)).val)]
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact le_rfl
  · exact pow_nonneg h0 _

/-- Every initial-clock amplitude dominates its non-wrapping partial history. -/
theorem historyAmplitude_initial_lower {N ell : ℕ} [NeZero N] (hN : ell ≤ N)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam < 1) (j : Fin N) (hj : j.val < ell) :
    ((1 + lam) / (1 - lam)) / Real.sqrt (ell : ℝ) *
      (1 - lam ^ (j.val + 1)) ≤ historyAmplitude ell lam j := by
  have he : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
  have hs : 0 < Real.sqrt (ell : ℝ) := Real.sqrt_pos.mpr he
  have hd : 0 < 1 - lam ^ N := by
    have h := pow_lt_one₀ h0 h1 (NeZero.ne N)
    linarith
  have hdle : 1 - lam ^ N ≤ 1 := by linarith [pow_nonneg h0 N]
  have hg : 0 < 1 - lam := by linarith
  have hpow : 0 ≤ 1 - lam ^ (j.val + 1) := by
    have h : lam ^ (j.val + 1) ≤ 1 := pow_le_one₀ h0 h1.le
    linarith
  have htarget : 0 ≤ ((1 + lam) / (1 - lam)) / Real.sqrt (ell : ℝ) *
      (1 - lam ^ (j.val + 1)) := by positivity
  have hscale : 0 ≤ (1 + lam) / (Real.sqrt (ell : ℝ) * (1 - lam ^ N)) := by positivity
  have hsum := mul_le_mul_of_nonneg_left (history_initial_partial_sum hN lam h0 j hj) hscale
  change (1 + lam) / (Real.sqrt (ell : ℝ) * (1 - lam ^ N)) *
    (∑ i : Fin (j.val + 1), lam ^ i.val) ≤ historyAmplitude ell lam j at hsum
  apply le_trans _ hsum
  rw [Fin.sum_univ_eq_sum_range, real_geometric_sum lam (j.val + 1) h1.ne]
  calc
    _ ≤ (((1 + lam) / (1 - lam)) / Real.sqrt (ell : ℝ) *
        (1 - lam ^ (j.val + 1))) / (1 - lam ^ N) := by
      apply (le_div_iff₀ hd).mpr
      exact mul_le_of_le_one_right htarget hdle
    _ = _ := by
      simp only [div_eq_mul_inv, _root_.mul_inv_rev]
      ring

/-- On the latter half of the source padding, every amplitude is at least
three quarters of kappa/sqrt(ell), for the paper's concrete parameters. -/
theorem historyAmplitude_plateau_lower {N : ℕ} [NeZero N] {kappa : ℝ} (hk : 4 ≤ kappa)
    (hN : historyPadding kappa ≤ N) (j : Fin N)
    (hjlo : historyPadding kappa / 2 ≤ j.val) (hjhi : j.val < historyPadding kappa) :
    3 * kappa / (4 * Real.sqrt (historyPadding kappa : ℝ)) ≤
      historyAmplitude (historyPadding kappa) (historyLambda kappa) j := by
  have h := historyAmplitude_initial_lower hN (historyLambda kappa)
    (historyLambda_nonneg hk) (historyLambda_lt_one hk) j hjhi
  rw [historyLambda_ratio hk] at h
  have hp : historyLambda kappa ^ (j.val + 1) ≤ 1 / 4 := by
    apply le_trans _ (historyLambda_pow_halfPadding_le hk)
    exact pow_le_pow_of_le_one (historyLambda_nonneg hk)
      (historyLambda_lt_one hk).le (by omega)
  have hs : 0 < Real.sqrt (historyPadding kappa : ℝ) := by
    apply Real.sqrt_pos.mpr
    exact_mod_cast historyPadding_pos hk
  have hks : 0 ≤ kappa / Real.sqrt (historyPadding kappa : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left (show (3 / 4 : ℝ) ≤ 1 -
      historyLambda kappa ^ (j.val + 1) by linarith) hks
  calc
    _ = kappa / Real.sqrt (historyPadding kappa : ℝ) * (3 / 4) := by ring
    _ ≤ _ := hmul.trans h

end OptimalQLS.LowerBounds
