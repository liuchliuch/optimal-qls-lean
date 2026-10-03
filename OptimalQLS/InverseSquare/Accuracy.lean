import OptimalQLS.InverseSquare.Surrogate
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-! # Quantitative accuracy of the uncompressed bounded surrogate -/
noncomputable section
namespace OptimalQLS.InverseSquare
open Polynomial Finset

/-- A rational bound leaves a fixed gap above the majority threshold. -/
theorem exp_neg_three_quarters : Real.exp (-(3 / 4 : ℝ)) ≤ 32 / 65 := by
  have h := Real.add_one_le_exp (3 / 32 : ℝ)
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 32 + 1) h 8
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  have he : 0 < Real.exp (3 / 4 : ℝ) := Real.exp_pos _
  rw [Real.exp_neg]
  rw [← one_div]
  apply (div_le_iff₀ he).mpr
  nlinarith

/-- The geometric map enters a fixed majority-success region. -/
theorem surrogate_signal_lower {δ x : ℝ} {M : ℕ}
    (hδ0 : 0 < δ) (hM : (3 / 4 : ℝ) ≤ δ ^ 2 * M)
    (hx0 : δ ≤ |x|) (hx1 : |x| ≤ 1) :
    (33 / 65 : ℝ) ≤ 1 - (1 - x ^ 2) ^ M := by
  have ht0 : 0 ≤ 1 - x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
  have hxδ : δ ^ 2 ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
  have hprod := mul_le_mul_of_nonneg_right hxδ (show (0 : ℝ) ≤ M by positivity)
  have hp := pow_le_pow_left₀ ht0 (Real.one_sub_le_exp_neg (x ^ 2)) M
  rw [← Real.exp_nat_mul] at hp
  have he : Real.exp ((M : ℝ) * -(x ^ 2)) ≤ Real.exp (-(3 / 4 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hh := hp.trans (he.trans exp_neg_three_quarters)
  linarith

theorem majority_failure_fixed (k : ℕ) {s : ℝ}
    (hs : (33 / 65 : ℝ) ≤ s) (hs1 : s ≤ 1) :
    1 - (majority k).eval s ≤ (4224 / 4225 : ℝ) ^ k := by
  have hhalf : (1 / 2 : ℝ) ≤ s := by linarith
  apply (majority_failure k hhalf hs1).trans
  apply pow_le_pow_left₀
  · exact mul_nonneg (by linarith) (by linarith)
  · nlinarith [sq_nonneg (s - 33 / 65)]

/-- Exact target scaling, with a geometric accuracy bound. -/
theorem surrogate_error {δ x : ℝ} (M k : ℕ)
    (hδ0 : 0 < δ) (hM : (3 / 4 : ℝ) ≤ δ ^ 2 * M)
    (hx0 : δ ≤ |x|) (hx1 : |x| ≤ 1) :
    |(surrogate δ M k).eval x - δ ^ 2 / (2 * x ^ 2)| ≤
      (1 / 2 : ℝ) * (4224 / 4225 : ℝ) ^ k := by
  have hxabs : 0 < |x| := lt_of_lt_of_le hδ0 hx0
  have hxne : x ≠ 0 := abs_pos.mp hxabs
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hxne
  have ht0 : 0 ≤ 1 - x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
  have hsig := surrogate_signal_lower hδ0 hM hx0 hx1
  have hs1 : 1 - (1 - x ^ 2) ^ M ≤ 1 := by linarith [pow_nonneg ht0 M]
  have hs0 : 0 ≤ 1 - (1 - x ^ 2) ^ M := by linarith
  have hH0 := majority_nonneg k hs0 hs1
  have hH1 := majority_le_one k hs0 hs1
  have htail := majority_failure_fixed k hsig hs1
  have hid := surrogate_mul_sq δ x M k
  have hpoint : (surrogate δ M k).eval x = δ ^ 2 / (2 * x ^ 2) *
      (majority k).eval (1 - (1 - x ^ 2) ^ M) := by
    apply (mul_right_cancel₀ (ne_of_gt hx2))
    rw [hid]
    field_simp
  have hc0 : 0 ≤ δ ^ 2 / (2 * x ^ 2) := by positivity
  have hc1 : δ ^ 2 / (2 * x ^ 2) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * x ^ 2)).mpr
    nlinarith [sq_abs x, abs_nonneg x]
  rw [hpoint, ← mul_sub_one, abs_mul, abs_of_nonneg hc0,
    abs_of_nonpos (sub_nonpos.mpr hH1)]
  have ht0 : 0 ≤ (4224 / 4225 : ℝ) ^ k := by positivity
  nlinarith [mul_le_mul hc1 htail (by linarith :
    0 ≤ 1 - (majority k).eval (1 - (1 - x ^ 2) ^ M)) (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-- The concrete majority order, with a deliberately conservative constant. -/
def majorityOrder (η : ℝ) : ℕ := ⌈4225 * Real.log (2 / η)⌉₊

theorem majorityOrder_tail {η : ℝ} (hη : 0 < η) :
    (1 / 2 : ℝ) * (4224 / 4225 : ℝ) ^ majorityOrder η ≤ η / 4 := by
  have hc : (4224 / 4225 : ℝ) ≤ Real.exp (-(1 / 4225 : ℝ)) := by
    convert Real.one_sub_le_exp_neg (1 / 4225 : ℝ) using 1; norm_num
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4224 / 4225) hc (majorityOrder η)
  rw [← Real.exp_nat_mul] at hp
  have ho : 4225 * Real.log (2 / η) ≤ (majorityOrder η : ℝ) := Nat.le_ceil _
  have he : Real.exp ((majorityOrder η : ℝ) * -(1 / 4225 : ℝ)) ≤
      Real.exp (-Real.log (2 / η)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have heq : Real.exp (-Real.log (2 / η)) = η / 2 := by
    rw [Real.exp_neg, Real.exp_log (div_pos (by norm_num) hη)]
    field_simp
  rw [heq] at he
  linarith [hp.trans he]

end OptimalQLS.InverseSquare
