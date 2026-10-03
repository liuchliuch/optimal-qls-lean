import OptimalQLS.LowerBounds.HistoryInitialBounds

/-! The lower endpoint `kappa/2` of the actual source-solution norm. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix

lemma sum_fin_middle_segment (N ell r : ℕ) (hr : r ≤ ell) (hN : ell ≤ N) (a : ℝ) :
    (∑ j : Fin N, if r ≤ j.val ∧ j.val < ell then a else 0) = (ell - r : ℕ) * a := by
  have heq : (∑ j : Fin N, if r ≤ j.val ∧ j.val < ell then a else 0) =
      (∑ j : Fin N, if j.val < ell then a else 0) -
        ∑ j : Fin N, if j.val < r then a else 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hlow : r ≤ j.val
    · by_cases hhi : j.val < ell <;> simp [hlow, hhi, not_lt.mpr hlow]
    · have hri : j.val < r := by omega
      have hei : j.val < ell := by omega
      simp [hlow, hri, hei]
  rw [heq, sum_fin_initial_segment N ell hN (fun _ => a),
    sum_fin_initial_segment N r (hr.trans hN) (fun _ => a)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Nat.cast_sub hr]
  ring

/-- The explicit plateau contributes at least `9 kappa²/32` to squared norm. -/
theorem history_amplitude_sum_sq_lower {N : ℕ} [NeZero N] {kappa : ℝ}
    (hk : 4 ≤ kappa) (hN : historyPadding kappa ≤ N) :
    9 * kappa ^ 2 / 32 ≤
      ∑ j : Fin N, (historyAmplitude (historyPadding kappa) (historyLambda kappa) j) ^ 2 := by
  let ell := historyPadding kappa
  let c := 3 * kappa / (4 * Real.sqrt (ell : ℝ))
  have hell : 0 < ell := historyPadding_pos hk
  have he : (0 : ℝ) < ell := by exact_mod_cast hell
  have hs : 0 < Real.sqrt (ell : ℝ) := Real.sqrt_pos.mpr he
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hsum : (∑ j : Fin N, if ell / 2 ≤ j.val ∧ j.val < ell then c ^ 2 else 0) ≤
      ∑ j : Fin N, (historyAmplitude ell (historyLambda kappa) j) ^ 2 := by
    apply Finset.sum_le_sum
    intro j _
    split_ifs with hj
    · have h := historyAmplitude_plateau_lower hk hN j hj.1 hj.2
      change c ≤ historyAmplitude ell (historyLambda kappa) j at h
      exact pow_le_pow_left₀ hc h 2
    · exact sq_nonneg _
  rw [sum_fin_middle_segment N ell (ell / 2) (by omega) hN] at hsum
  have hcountNat : ell ≤ 2 * (ell - ell / 2) := by omega
  have hcount : (ell : ℝ) / 2 ≤ (ell - ell / 2 : ℕ) := by
    have hh : (ell : ℝ) ≤ 2 * (ell - ell / 2 : ℕ) := by exact_mod_cast hcountNat
    linarith
  have hhalf := mul_le_mul_of_nonneg_right hcount (sq_nonneg c)
  have heq : (ell : ℝ) / 2 * c ^ 2 = 9 * kappa ^ 2 / 32 := by
    dsimp [c]
    have hs2 : (Real.sqrt (ell : ℝ)) ^ 2 = ell := Real.sq_sqrt he.le
    field_simp
    nlinarith
  rw [heq] at hhalf
  exact hhalf.trans hsum

/-- The actual normalized-source solution has norm at least `kappa/2`.
This is a theorem about the explicit inverse matrix, not a promise field. -/
theorem history_source_solution_norm_lower {N : ℕ} [NeZero N] {kappa : ℝ}
    (hk : 4 ≤ kappa) (hN : historyPadding kappa ≤ N) (profile : Fin N → Bool)
    (hfixed : ∀ j : Fin N, j.val < historyPadding kappa → profile j = false) :
    kappa / 2 ≤ ‖WithLp.toLp 2 (historyInverse profile (historyLambda kappa : ℂ) *ᵥ
      uniformHistorySource (historyPadding kappa))‖ := by
  have hlam0 := historyLambda_nonneg hk
  have hlam1 := historyLambda_lt_one hk
  have hplus : (1 : ℂ) + (historyLambda kappa : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show (0 : ℝ) < 1 + historyLambda kappa by linarith))
  have hden := history_geometric_denominator_ne_zero (N := N) (historyLambda kappa) hlam0 hlam1
  have hsq := history_solution_norm_sq_amplitudes profile hfixed hN (historyLambda kappa) hplus hden
  have hlower := history_amplitude_sum_sq_lower hk hN
  rw [← hsq] at hlower
  have hn := norm_nonneg (WithLp.toLp 2 (historyInverse profile (historyLambda kappa : ℂ) *ᵥ
    uniformHistorySource (historyPadding kappa)))
  nlinarith

/-- Both endpoints of the paper's solution-norm interval, for every source-fixed gauge. -/
theorem history_source_solution_norm_bounds {N : ℕ} [NeZero N] {kappa : ℝ}
    (hk : 4 ≤ kappa) (hN : historyPadding kappa ≤ N) (profile : Fin N → Bool)
    (hfixed : ∀ j : Fin N, j.val < historyPadding kappa → profile j = false) :
    kappa / 2 ≤ ‖WithLp.toLp 2 (historyInverse profile (historyLambda kappa : ℂ) *ᵥ
      uniformHistorySource (historyPadding kappa))‖ ∧
    ‖WithLp.toLp 2 (historyInverse profile (historyLambda kappa : ℂ) *ᵥ
      uniformHistorySource (historyPadding kappa))‖ ≤ kappa := by
  constructor
  · exact history_source_solution_norm_lower hk hN profile hfixed
  · have h := history_source_solution_norm_le profile (historyPadding_pos hk) hN
      (historyLambda kappa) (historyLambda_nonneg hk) (historyLambda_lt_one hk)
    simpa only [historyLambda_ratio hk] using h

end OptimalQLS.LowerBounds
