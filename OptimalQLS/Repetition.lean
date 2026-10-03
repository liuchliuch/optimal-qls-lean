import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

set_option maxHeartbeats 10000
namespace OptimalQLS

/-- A short rational Taylor certificate verifies the unusually tight
72000-run constant; no floating-point approximation is trusted. -/
theorem three_lt_exp_repetition_constant : (3 : ℝ) < Real.exp (72000 / 65536) := by
  have heq : (72000 : ℝ) / 65536 = 1125 / 1024 := by norm_num
  rw [heq]
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1125 / 1024 by norm_num) 10
  apply lt_of_lt_of_le _ h
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.factorial_succ, Nat.factorial_zero]


/-- The elementary independent-failure estimate, with symbolic repetition
count so elaboration never expands the 72000th power. -/
theorem failure_power_le_exp {p : ℝ} (hp1 : p ≤ 1) (n : ℕ) :
    (1 - p) ^ n ≤ Real.exp (n * (-p)) := by
  have hbasic : 1 - p ≤ Real.exp (-p) := by
    have h := Real.add_one_le_exp (-p)
    linarith
  calc
    (1 - p) ^ n ≤ Real.exp (-p) ^ n := pow_le_pow_left₀ (sub_nonneg.mpr hp1) hbasic n
    _ = Real.exp (n * (-p)) := (Real.exp_nat_mul (-p) n).symm

/-- With the actual per-run success lower bound, 72000 independent runs
have total failure probability less than one third. -/
theorem repetition_failure_bound {p : ℝ} (hp : 1 / 65536 < p) (hp1 : p ≤ 1) :
    (1 - p) ^ 72000 < 1 / 3 := by
  have hexp : Real.exp ((72000 : ℕ) * (-p)) ≤ Real.exp (-(72000 / 65536)) := by
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    linarith
  refine lt_of_le_of_lt ((failure_power_le_exp hp1 72000).trans hexp) ?_
  rw [Real.exp_neg]
  have h := three_lt_exp_repetition_constant
  simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 3) h

end OptimalQLS
