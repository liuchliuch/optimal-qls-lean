import OptimalQLS.LowerBounds.HistoryNormExact
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Elementary quantitative bounds for the history parameters

These polynomial estimates avoid relying on an unformalized exponential
approximation. They imply the quarter/half decay bounds needed by the
source-profile and parity-tail calculations.
-/
noncomputable section
namespace OptimalQLS.LowerBounds

def historyLambda (kappa : ℝ) : ℝ := (kappa - 1) / (kappa + 1)
def historyPadding (kappa : ℝ) : ℕ := ⌈8 * kappa⌉₊

theorem historyLambda_nonneg {kappa : ℝ} (hk : 4 ≤ kappa) : 0 ≤ historyLambda kappa := by
  unfold historyLambda
  exact div_nonneg (by linarith) (by linarith)

theorem historyLambda_lt_one {kappa : ℝ} (hk : 4 ≤ kappa) : historyLambda kappa < 1 := by
  unfold historyLambda
  apply (div_lt_one (by linarith : 0 < kappa + 1)).mpr
  linarith

theorem historyLambda_ratio {kappa : ℝ} (hk : 4 ≤ kappa) :
    (1 + historyLambda kappa) / (1 - historyLambda kappa) = kappa := by
  unfold historyLambda
  field_simp
  ring

theorem historyLambda_gap {kappa : ℝ} (hk : 4 ≤ kappa) :
    1 - historyLambda kappa = 2 / (kappa + 1) := by
  unfold historyLambda
  field_simp
  ring

/-- Rational bound on geometric powers, proved by an elementary induction. -/
theorem pow_mul_linear_decay_le_one (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (n : ℕ) :
    lam ^ n * (1 + (n : ℝ) * (1 - lam)) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 0 ≤ lam ^ n := pow_nonneg h0 n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have he : 0 ≤ (n : ℝ) * lam ^ n * (1 - lam) ^ 2 := by positivity
    simp only [pow_succ, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem pow_le_quarter_of_gap (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (n : ℕ)
    (hgap : 3 ≤ (n : ℝ) * (1 - lam)) : lam ^ n ≤ 1 / 4 := by
  have h := pow_mul_linear_decay_le_one lam h0 h1 n
  have hp : 0 ≤ lam ^ n := pow_nonneg h0 n
  nlinarith

theorem historyPadding_lower {kappa : ℝ} (hk : 4 ≤ kappa) :
    8 * kappa ≤ (historyPadding kappa : ℝ) :=
  Nat.le_ceil _

theorem historyPadding_upper {kappa : ℝ} (hk : 4 ≤ kappa) :
    (historyPadding kappa : ℝ) ≤ 9 * kappa := by
  have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 8 * kappa by linarith)
  change (historyPadding kappa : ℝ) < 8 * kappa + 1 at h
  linarith

theorem historyPadding_pos {kappa : ℝ} (hk : 4 ≤ kappa) : 0 < historyPadding kappa := by
  have h := historyPadding_lower hk
  by_contra hn
  have he : historyPadding kappa = 0 := by omega
  simp [he] at h
  linarith

/-- Already the integer half-padding suppresses the geometric factor to1/4. -/
theorem historyLambda_pow_halfPadding_le {kappa : ℝ} (hk : 4 ≤ kappa) :
    historyLambda kappa ^ (historyPadding kappa / 2) ≤ 1 / 4 := by
  apply pow_le_quarter_of_gap _ (historyLambda_nonneg hk) (historyLambda_lt_one hk).le
  rw [historyLambda_gap hk]
  have hlow := historyPadding_lower hk
  have hdiv : historyPadding kappa ≤ 2 * (historyPadding kappa / 2) + 1 := by omega
  have hdivR : (historyPadding kappa : ℝ) ≤ 2 * (historyPadding kappa / 2 : ℕ) + 1 := by
    exact_mod_cast hdiv
  have hden : 0 < kappa + 1 := by linarith
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hden).mpr
  nlinarith

theorem historyLambda_pow_padding_le_half {kappa : ℝ} (hk : 4 ≤ kappa) :
    historyLambda kappa ^ historyPadding kappa ≤ 1 / 2 := by
  have hpow := historyLambda_pow_halfPadding_le hk
  have hmono : historyLambda kappa ^ historyPadding kappa ≤
      historyLambda kappa ^ (historyPadding kappa / 2) :=
    pow_le_pow_of_le_one (historyLambda_nonneg hk) (historyLambda_lt_one hk).le (by omega)
  linarith

end OptimalQLS.LowerBounds
