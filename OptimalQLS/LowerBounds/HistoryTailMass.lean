import OptimalQLS.LowerBounds.HistoryTailScalars

/-! The literal tail clock interval has the paper's quantitative squared mass. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix

/-- Clock `ell + m - 1 + k`, the k-th outcome in the parity interval. -/
def tailClock {N ell m : ℕ} (hell : 0 < ell) (hN : 2 * ell + m ≤ N) (k : Fin ell) : Fin N :=
  ⟨ell + m - 1 + k.val, by omega⟩

theorem tailClock_injective {N ell m : ℕ} (hell : 0 < ell) (hN : 2 * ell + m ≤ N) :
    Function.Injective (tailClock hell hN) := by
  intro i j hij
  have h := congrArg Fin.val hij
  apply Fin.ext
  dsimp [tailClock] at h
  omega

def tailAmplitudeMass {N ell m : ℕ} [NeZero N] (hell : 0 < ell)
    (hN : 2 * ell + m ≤ N) (lam : ℝ) : ℝ :=
  ∑ k : Fin ell, historyAmplitude ell lam (tailClock hell hN k) ^ 2

/-- Unnormalized tail mass has an explicit kappa²-scaled lower bound. -/
theorem tailAmplitudeMass_lower {N m : ℕ} [NeZero N] {kappa : ℝ} (hk : 4 ≤ kappa)
    (hN : 2 * historyPadding kappa + m ≤ N) :
    kappa ^ 2 * historyLambda kappa ^ (2 * m) / 256 ≤
      tailAmplitudeMass (historyPadding_pos hk) hN (historyLambda kappa) := by
  let ell := historyPadding kappa
  let lam := historyLambda kappa
  have hell : 0 < ell := historyPadding_pos hk
  have hNe : ell ≤ N := by dsimp [ell]; omega
  have h0 : 0 ≤ lam := historyLambda_nonneg hk
  have h1 : lam < 1 := historyLambda_lt_one hk
  have he : (0 : ℝ) < ell := by exact_mod_cast hell
  have hs : 0 < Real.sqrt (ell : ℝ) := Real.sqrt_pos.mpr he
  have hgap : 0 ≤ 1 - lam ^ ell := by
    have h : lam ^ ell ≤ 1 := pow_le_one₀ h0 h1.le
    linarith
  have hsum : (∑ k : Fin ell,
      (lam ^ (m + k.val) * kappa / Real.sqrt (ell : ℝ) * (1 - lam ^ ell)) ^ 2) ≤
      tailAmplitudeMass hell hN lam := by
    apply Finset.sum_le_sum
    intro k _
    have ht := historyAmplitude_tail_lower hell hNe lam h0 h1 (tailClock hell hN k)
      (by dsimp [tailClock]; omega)
    have hexp : (tailClock hell hN k).val + 1 - ell = m + k.val := by
      dsimp [tailClock]; omega
    rw [hexp, historyLambda_ratio hk] at ht
    have hpos : 0 ≤ lam ^ (m + k.val) * kappa / Real.sqrt (ell : ℝ) * (1 - lam ^ ell) := by
      positivity
    exact pow_le_pow_left₀ hpos ht 2
  have hfactor : (∑ k : Fin ell,
      (lam ^ (m + k.val) * kappa / Real.sqrt (ell : ℝ) * (1 - lam ^ ell)) ^ 2) =
      (kappa ^ 2 * lam ^ (2 * m)) *
        (((1 - lam ^ ell) ^ 2 / (ell : ℝ)) * ∑ k : Fin ell, (lam ^ 2) ^ k.val) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [pow_add, mul_pow, div_pow, Real.sq_sqrt he.le, ← pow_mul]
    simp only [Nat.mul_comm]
    ring
  rw [hfactor] at hsum
  have hcoeff := history_tail_coefficient_lower hk
  have hmul := mul_le_mul_of_nonneg_left hcoeff
    (mul_nonneg (sq_nonneg kappa) (pow_nonneg h0 (2 * m)))
  have hfirst : kappa ^ 2 * lam ^ (2 * m) / 256 ≤
      (kappa ^ 2 * lam ^ (2 * m)) *
        (((1 - lam ^ ell) ^ 2 / (ell : ℝ)) * ∑ k : Fin ell, (lam ^ 2) ^ k.val) := by
    simpa [ell, lam, div_eq_mul_inv] using hmul
  exact hfirst.trans hsum

/-- Dividing by the actual solution norm yields the required1/256 factor. -/
theorem normalized_tail_mass_lower {N m : ℕ} [NeZero N] {kappa : ℝ} (hk : 4 ≤ kappa)
    (hN : 2 * historyPadding kappa + m ≤ N) (profile : Fin N → Bool)
    (hfixed : ∀ j : Fin N, j.val < historyPadding kappa → profile j = false) :
    historyLambda kappa ^ (2 * m) / 256 ≤
      tailAmplitudeMass (historyPadding_pos hk) hN (historyLambda kappa) /
        ‖WithLp.toLp 2 (historyInverse profile (historyLambda kappa : ℂ) *ᵥ
          uniformHistorySource (historyPadding kappa))‖ ^ 2 := by
  have hNe : historyPadding kappa ≤ N := by omega
  have hnorm := history_source_solution_norm_bounds hk hNe profile hfixed
  let Y := ‖WithLp.toLp 2 (historyInverse profile (historyLambda kappa : ℂ) *ᵥ
    uniformHistorySource (historyPadding kappa))‖
  have hy : 0 < Y := by dsimp [Y]; linarith [hnorm.1]
  have hyk : Y ^ 2 ≤ kappa ^ 2 := by
    have hupper : Y ≤ kappa := hnorm.2
    nlinarith
  have ht := tailAmplitudeMass_lower (m := m) hk hN
  have hp : 0 ≤ historyLambda kappa ^ (2 * m) / 256 := by
    exact div_nonneg (pow_nonneg (historyLambda_nonneg hk) _) (by norm_num)
  change _ ≤ _ / Y ^ 2
  apply (le_div_iff₀ (sq_pos_of_pos hy)).mpr
  have hmul := mul_le_mul_of_nonneg_left hyk hp
  calc
    _ ≤ historyLambda kappa ^ (2 * m) / 256 * kappa ^ 2 := hmul
    _ = kappa ^ 2 * historyLambda kappa ^ (2 * m) / 256 := by ring
    _ ≤ _ := ht

end OptimalQLS.LowerBounds
