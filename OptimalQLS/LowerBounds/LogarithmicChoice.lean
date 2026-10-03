import OptimalQLS.LowerBounds.HistoryPowerBounds
import OptimalQLS.LowerBounds.HardFamilySignal
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Explicit logarithmic hard-family parameters

For `κ ≥ 8` and `0 < ε ≤ exp (-16)`, choosing
`m = floor (κ log (1 / ε) / 48)` preserves more than four times the solver
error in the literal `5 / 2304` parity signal. The floor remains at least
`κ log (1 / ε) / 96`, and the actual dilated matrix dimension is at most
`9 κ log (1 / ε)`.
-/

noncomputable section
namespace OptimalQLS.LowerBounds

/-- The concrete bit-string length used for the logarithmic lower bound. -/
def logarithmicParityLength (kappa eps : ℝ) : ℕ :=
  ⌊kappa * Real.log (1 / eps) / 48⌋₊

/-- The clock size for the concrete logarithmic choice. -/
def logarithmicHistorySize (kappa eps : ℝ) : ℕ :=
  2 * historyPadding kappa + 2 * logarithmicParityLength kappa eps

theorem logarithmic_accuracy_log_lower {eps : ℝ} (heps : 0 < eps)
    (hsmall : eps ≤ Real.exp (-16)) : 16 ≤ Real.log (1 / eps) := by
  have h := Real.log_le_log heps hsmall
  rw [Real.log_exp] at h
  simpa only [one_div, Real.log_inv] using (show 16 ≤ -Real.log eps by linarith)

/-- A direct rational bound gives the needed logarithmic decay estimate. -/
theorem historyLambda_log_lower {kappa : ℝ} (hk : 4 ≤ kappa) :
    -3 / kappa ≤ Real.log (historyLambda kappa) := by
  have hkpos : 0 < kappa := by linarith
  have hkminus : 0 < kappa - 1 := by linarith
  have hlam : 0 < historyLambda kappa := by
    exact div_pos hkminus (by linarith)
  have hrat : 2 / (kappa - 1) ≤ 3 / kappa := by
    apply (div_le_div_iff₀ hkminus hkpos).mpr
    nlinarith
  have heq : 1 - (historyLambda kappa)⁻¹ = -(2 / (kappa - 1)) := by
    unfold historyLambda
    rw [inv_div]
    field_simp
    ring
  have hlog := Real.one_sub_inv_le_log_of_pos hlam
  rw [heq] at hlog
  rw [neg_div]
  exact (neg_le_neg hrat).trans hlog

theorem logarithmicParityLength_bounds {kappa eps : ℝ} (hk : 8 ≤ kappa)
    (heps : 0 < eps) (hsmall : eps ≤ Real.exp (-16)) :
    1 ≤ logarithmicParityLength kappa eps ∧
      kappa * Real.log (1 / eps) / 96 ≤ (logarithmicParityLength kappa eps : ℝ) ∧
      (logarithmicParityLength kappa eps : ℝ) ≤ kappa * Real.log (1 / eps) / 48 := by
  have ht := logarithmic_accuracy_log_lower heps hsmall
  have hprod : 128 ≤ kappa * Real.log (1 / eps) := by nlinarith
  have hnonneg : 0 ≤ kappa * Real.log (1 / eps) / 48 := by positivity
  have hupper := Nat.floor_le hnonneg
  have hlower := Nat.lt_floor_add_one (kappa * Real.log (1 / eps) / 48)
  refine ⟨?_, ?_, hupper⟩
  · unfold logarithmicParityLength
    apply (Nat.one_le_floor_iff _).mpr
    linarith
  · change kappa * Real.log (1 / eps) / 96 ≤
      (⌊kappa * Real.log (1 / eps) / 48⌋₊ : ℝ)
    linarith

theorem logarithmicParityLength_power_lower {kappa eps : ℝ} (hk : 8 ≤ kappa)
    (heps : 0 < eps) (hsmall : eps ≤ Real.exp (-16)) :
    Real.exp (-Real.log (1 / eps) / 8) ≤
      historyLambda kappa ^ (2 * logarithmicParityLength kappa eps) := by
  have hkpos : 0 < kappa := by linarith
  have hk4 : 4 ≤ kappa := by linarith
  have hlog := historyLambda_log_lower hk4
  have hm := (logarithmicParityLength_bounds hk heps hsmall).2.2
  have hscaled := mul_le_mul_of_nonneg_left hlog
    (show (0 : ℝ) ≤ 2 * (logarithmicParityLength kappa eps : ℝ) by positivity)
  have hquot : -Real.log (1 / eps) / 8 ≤
      (2 * (logarithmicParityLength kappa eps : ℝ)) * (-3 / kappa) := by
    rw [show (2 * (logarithmicParityLength kappa eps : ℝ)) * (-3 / kappa) =
      (-6 * (logarithmicParityLength kappa eps : ℝ)) / kappa by ring]
    apply (le_div_iff₀ hkpos).mpr
    nlinarith
  have hlam : 0 < historyLambda kappa := by
    unfold historyLambda
    exact div_pos (by linarith) (by linarith)
  calc
    Real.exp (-Real.log (1 / eps) / 8) ≤
        Real.exp ((2 * (logarithmicParityLength kappa eps : ℝ)) *
          Real.log (historyLambda kappa)) := Real.exp_le_exp.mpr (hquot.trans hscaled)
    _ = historyLambda kappa ^ (2 * logarithmicParityLength kappa eps) := by
      rw [show (2 * (logarithmicParityLength kappa eps : ℝ)) =
        ((2 * logarithmicParityLength kappa eps : ℕ) : ℝ) by push_cast; ring]
      rw [Real.exp_nat_mul, Real.exp_log hlam]

/-- A fully numerical separation constant, with no asymptotic premise. -/
theorem logarithmic_signal_strict {kappa eps : ℝ} (hk : 8 ≤ kappa)
    (heps : 0 < eps) (hsmall : eps ≤ Real.exp (-16)) :
    4 * eps < (5 / 2304 : ℝ) *
      historyLambda kappa ^ (2 * logarithmicParityLength kappa eps) := by
  have ht := logarithmic_accuracy_log_lower heps hsmall
  have hexp2 : (3 : ℝ) ≤ Real.exp 2 := by
    linarith [Real.add_one_le_exp (2 : ℝ)]
  have hexp14 : (2187 : ℝ) ≤ Real.exp 14 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hexp2 7
    have heq : Real.exp (14 : ℝ) = Real.exp 2 ^ (7 : ℕ) := by
      convert Real.exp_nat_mul (2 : ℝ) 7 using 1
      norm_num
    rw [heq]
    norm_num at h ⊢
    exact h
  have hlarge : (1843.2 : ℝ) < Real.exp (7 * Real.log (1 / eps) / 8) := by
    have hmono : Real.exp (14 : ℝ) ≤ Real.exp (7 * Real.log (1 / eps) / 8) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  have heq : Real.exp (-Real.log (1 / eps) / 8) =
      eps * Real.exp (7 * Real.log (1 / eps) / 8) := by
    have hepslog : Real.exp (-Real.log (1 / eps)) = eps := by
      simp only [one_div, Real.log_inv, neg_neg]
      exact Real.exp_log heps
    calc
      Real.exp (-Real.log (1 / eps) / 8) =
          Real.exp (-Real.log (1 / eps) + 7 * Real.log (1 / eps) / 8) := by
        congr 1
        ring
      _ = _ := by rw [Real.exp_add, hepslog]
  have hbase : 4 * eps < (5 / 2304 : ℝ) * Real.exp (-Real.log (1 / eps) / 8) := by
    rw [heq]
    nlinarith [mul_lt_mul_of_pos_left hlarge heps]
  exact hbase.trans_le (mul_le_mul_of_nonneg_left
    (logarithmicParityLength_power_lower hk heps hsmall) (by norm_num))

theorem logarithmicHistorySize_pos {kappa eps : ℝ} (hk : 8 ≤ kappa)
    (heps : 0 < eps) (hsmall : eps ≤ Real.exp (-16)) :
    0 < logarithmicHistorySize kappa eps := by
  have hm := (logarithmicParityLength_bounds hk heps hsmall).1
  unfold logarithmicHistorySize
  omega

theorem logarithmicHistorySize_upper {kappa eps : ℝ} (hk : 8 ≤ kappa)
    (heps : 0 < eps) (hsmall : eps ≤ Real.exp (-16)) :
    (logarithmicHistorySize kappa eps : ℝ) ≤ 2 * kappa * Real.log (1 / eps) := by
  have ht := logarithmic_accuracy_log_lower heps hsmall
  have hm := (logarithmicParityLength_bounds hk heps hsmall).2.2
  have hp := historyPadding_upper (show 4 ≤ kappa by linarith)
  unfold logarithmicHistorySize
  push_cast
  nlinarith

/-- The matrix dimension itself has an explicit `O(κ log(1/ε))` bound. -/
theorem logarithmicHardFamily_dimension_upper {kappa eps : ℝ} (hk : 8 ≤ kappa)
    (heps : 0 < eps) (hsmall : eps ≤ Real.exp (-16)) :
    (Fintype.card (HardFamilyIndex (logarithmicHistorySize kappa eps)) : ℝ) ≤
      9 * kappa * Real.log (1 / eps) := by
  rw [hardFamily_dimension]
  push_cast
  have hN := logarithmicHistorySize_upper hk heps hsmall
  have ht := logarithmic_accuracy_log_lower heps hsmall
  have hprod : 128 ≤ kappa * Real.log (1 / eps) := by nlinarith
  nlinarith

/-- Explicit witnesses for all parameter requirements in the logarithmic
matrix-query argument, including the size of the actual matrix index type. -/
theorem exists_logarithmic_hard_family_parameters {kappa eps : ℝ} (hk : 8 ≤ kappa)
    (heps : 0 < eps) (hsmall : eps ≤ Real.exp (-16)) :
    ∃ m N : ℕ,
      1 ≤ m ∧
      kappa * Real.log (1 / eps) / 96 ≤ (m : ℝ) ∧
      (m : ℝ) ≤ kappa * Real.log (1 / eps) / 48 ∧
      4 * eps < (5 / 2304 : ℝ) * historyLambda kappa ^ (2 * m) ∧
      N = 2 * historyPadding kappa + 2 * m ∧
      0 < N ∧
      (Fintype.card (HardFamilyIndex N) : ℝ) ≤ 9 * kappa * Real.log (1 / eps) := by
  have hm := logarithmicParityLength_bounds hk heps hsmall
  exact ⟨logarithmicParityLength kappa eps, logarithmicHistorySize kappa eps,
    hm.1, hm.2.1, hm.2.2, logarithmic_signal_strict hk heps hsmall, rfl,
    logarithmicHistorySize_pos hk heps hsmall,
    logarithmicHardFamily_dimension_upper hk heps hsmall⟩

end OptimalQLS.LowerBounds
