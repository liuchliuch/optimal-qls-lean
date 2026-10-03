import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Bounded binomial-majority polynomials

These are an explicit algebraic ingredient of the inverse-square construction.
The Markov bound has a constant independent of the majority order.
-/
noncomputable section
namespace OptimalQLS.InverseSquare
open Polynomial Finset

/-- Probability of a strict majority of successes among `2*k+1` trials. -/
def majority (k : ℕ) : ℝ[X] :=
  ∑ i ∈ range (k + 1), C (((2 * k + 1).choose i : ℕ) : ℝ) *
    X ^ (2 * k + 1 - i) * (1 - X) ^ i

@[simp] theorem majority_eval (k : ℕ) (s : ℝ) :
    (majority k).eval s = ∑ i ∈ range (k + 1),
      ((2 * k + 1).choose i : ℝ) * s ^ (2 * k + 1 - i) * (1 - s) ^ i := by
  simp only [majority, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one]

/-- The full binomial sum is exactly one. -/
theorem binomial_partition (n : ℕ) (s : ℝ) :
    (∑ i ∈ range (n + 1), (n.choose i : ℝ) * s ^ (n - i) * (1 - s) ^ i) = 1 := by
  have h := add_pow (1 - s) s n
  have heq : (1 - s) + s = 1 := by ring
  rw [heq, one_pow] at h
  convert h.symm using 1
  apply sum_congr rfl
  intro i hi
  ring

theorem majority_nonneg (k : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ (majority k).eval s := by
  rw [majority_eval]
  exact sum_nonneg fun i _ => mul_nonneg (mul_nonneg (by positivity)
    (pow_nonneg hs0 _)) (pow_nonneg (by linarith) _)

theorem majority_le_one (k : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (majority k).eval s ≤ 1 := by
  rw [majority_eval]
  conv_rhs => rw [← binomial_partition (2 * k + 1) s]
  apply sum_le_sum_of_subset_of_nonneg
  · exact range_mono (by omega)
  · intro i hi hni
    exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hs0 _))
      (pow_nonneg (by linarith) _)

/-- A row coefficient in the majority half is at most twice its predecessor. -/
theorem choose_majority_le (k i : ℕ) (hi : i ≤ k) :
    (2 * k + 1).choose i ≤ 2 * (2 * k).choose i := by
  have h := Nat.choose_mul_succ_eq (2 * k) i
  have hsub : k + 1 ≤ 2 * k + 1 - i := by omega
  have hp := Nat.mul_le_mul_left ((2 * k + 1).choose i) hsub
  nlinarith

/-- A degree-independent Markov bound. -/
theorem majority_le_two_mul (k : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (majority k).eval s ≤ 2 * s := by
  rw [majority_eval]
  have hterm : ∀ i ∈ range (k + 1),
      ((2 * k + 1).choose i : ℝ) * s ^ (2 * k + 1 - i) * (1 - s) ^ i ≤
      2 * s * (( (2 * k).choose i : ℝ) * s ^ (2 * k - i) * (1 - s) ^ i) := by
    intro i hi
    have hik : i ≤ k := by simpa using mem_range.mp hi
    have hexp : 2 * k + 1 - i = (2 * k - i) + 1 := by omega
    rw [hexp, pow_succ]
    have hc : ((2 * k + 1).choose i : ℝ) ≤ 2 * ((2 * k).choose i : ℝ) := by
      exact_mod_cast choose_majority_le k i hik
    have hh := mul_le_mul_of_nonneg_right hc
      (show 0 ≤ (s ^ (2 * k - i) * s) * (1 - s) ^ i by
        exact mul_nonneg (mul_nonneg (pow_nonneg hs0 _) hs0) (pow_nonneg (by linarith) _))
    nlinarith only [hh]
  calc
    _ ≤ ∑ i ∈ range (k + 1), 2 * s *
        (((2 * k).choose i : ℝ) * s ^ (2 * k - i) * (1 - s) ^ i) :=
      sum_le_sum hterm
    _ = 2 * s * ∑ i ∈ range (k + 1),
        (((2 * k).choose i : ℝ) * s ^ (2 * k - i) * (1 - s) ^ i) := by rw [mul_sum]
    _ ≤ 2 * s * ∑ i ∈ range (2 * k + 1),
        (((2 * k).choose i : ℝ) * s ^ (2 * k - i) * (1 - s) ^ i) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum_of_subset_of_nonneg
      · exact range_mono (by omega)
      · intro i hi hni
        exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hs0 _))
          (pow_nonneg (by linarith) _)
    _ = 2 * s := by rw [binomial_partition, mul_one]

/-- Complement symmetry of odd majority. -/
theorem majority_complement (k : ℕ) (s : ℝ) :
    (majority k).eval s + (majority k).eval (1 - s) = 1 := by
  let f : ℕ → ℝ := fun i => ((2 * k + 1).choose i : ℝ) *
    s ^ (2 * k + 1 - i) * (1 - s) ^ i
  have hreflect : (majority k).eval (1 - s) =
      ∑ i ∈ Ico (k + 1) (2 * k + 2), f i := by
    rw [majority_eval]
    have hh : ∑ i ∈ range (k + 1), f (2 * k + 1 - i) =
        ∑ i ∈ Ico (k + 1) (2 * k + 2), f i := by
      rw [range_eq_Ico, sum_Ico_reflect _ _ (by omega)]
      congr 2; omega
    rw [← hh]
    apply sum_congr rfl
    intro i hi
    have hil : i ≤ 2 * k + 1 := by have := mem_range.mp hi; omega
    dsimp [f]
    rw [Nat.choose_symm hil, Nat.sub_sub_self hil]
    have hs : 1 - (1 - s) = s := by ring
    rw [hs]
    ring
  rw [hreflect, majority_eval]
  change (∑ i ∈ range (k + 1), f i) +
    (∑ i ∈ Ico (k + 1) (2 * k + 2), f i) = 1
  rw [sum_range_add_sum_Ico _ (by omega)]
  exact binomial_partition (2 * k + 1) s

/-- Exponential-in-order elementary tail estimate without probability axioms. -/
theorem majority_failure (k : ℕ) {s : ℝ} (hs : 1 / 2 ≤ s) (hs1 : s ≤ 1) :
    1 - (majority k).eval s ≤ (4 * s * (1 - s)) ^ k := by
  have hs0 : 0 ≤ s := by linarith
  have ht0 : 0 ≤ 1 - s := by linarith
  have hts : 1 - s ≤ s := by linarith
  have hc := majority_complement k s
  have heq : 1 - (majority k).eval s = (majority k).eval (1 - s) := by linarith
  rw [heq, majority_eval]
  have hh : 1 - (1 - s) = s := by ring
  rw [hh]
  have hterm : ∀ i ∈ range (k + 1),
      ((2 * k + 1).choose i : ℝ) * (1 - s) ^ (2 * k + 1 - i) * s ^ i ≤
      ((2 * k + 1).choose i : ℝ) * ((1 - s) * (s * (1 - s)) ^ k) := by
    intro i hi
    have hik : i ≤ k := by simpa using mem_range.mp hi
    have he : 2 * k + 1 - i = k + (k - i) + 1 := by omega
    have he2 : k - i + i = k := Nat.sub_add_cancel hik
    have hp := pow_le_pow_left₀ ht0 hts (k - i)
    have hm := mul_le_mul_of_nonneg_right hp
      (show 0 ≤ (1 - s) ^ k * (1 - s) * s ^ i by positivity)
    have hepower : (1 - s) ^ (2 * k + 1 - i) =
        (1 - s) ^ k * (1 - s) ^ (k - i) * (1 - s) := by
      rw [he, pow_succ, pow_add]
    rw [hepower]
    have hb : (1 - s) ^ k * (1 - s) ^ (k - i) * (1 - s) * s ^ i ≤
        (1 - s) * (s * (1 - s)) ^ k := by
      calc
        _ ≤ s ^ (k - i) * ((1 - s) ^ k * (1 - s) * s ^ i) := by nlinarith only [hm]
        _ = (1 - s) * (s * (1 - s)) ^ k := by
          have hpow : s ^ (k - i) * s ^ i = s ^ k := by rw [← pow_add, he2]
          calc
            _ = (1 - s) * ((s ^ (k - i) * s ^ i) * (1 - s) ^ k) := by ring
            _ = _ := by rw [hpow, mul_pow]
    nlinarith only [mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ (2 * k + 1).choose i by positivity)]
  calc
    _ ≤ ∑ i ∈ range (k + 1), ((2 * k + 1).choose i : ℝ) *
        ((1 - s) * (s * (1 - s)) ^ k) := sum_le_sum hterm
    _ = (4 : ℝ) ^ k * ((1 - s) * (s * (1 - s)) ^ k) := by
      rw [← sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose_halfway k
    _ ≤ (4 : ℝ) ^ k * (s * (1 - s)) ^ k := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_of_le_one_left (by positivity) (by linarith)
    _ = (4 * s * (1 - s)) ^ k := by rw [← mul_pow]; congr 1; ring

/-- The majority polynomial with its factor X removed explicitly. -/
def majorityQuotient (k : ℕ) : ℝ[X] :=
  ∑ i ∈ range (k + 1), C (((2 * k + 1).choose i : ℕ) : ℝ) *
    X ^ (2 * k - i) * (1 - X) ^ i

@[simp] theorem majorityQuotient_eval (k : ℕ) (s : ℝ) :
    (majorityQuotient k).eval s = ∑ i ∈ range (k + 1),
      ((2 * k + 1).choose i : ℝ) * s ^ (2 * k - i) * (1 - s) ^ i := by
  simp only [majorityQuotient, eval_finset_sum, eval_mul, eval_C, eval_pow,
    eval_X, eval_sub, eval_one]

theorem majority_factor (k : ℕ) : majority k = X * majorityQuotient k := by
  unfold majority majorityQuotient
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  have hik : i ≤ k := by simpa using mem_range.mp hi
  rw [show 2 * k + 1 - i = (2 * k - i) + 1 by omega, pow_succ]
  ring

theorem majorityQuotient_nonneg (k : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ (majorityQuotient k).eval s := by
  rw [majorityQuotient_eval]
  exact sum_nonneg fun i _ => mul_nonneg (mul_nonneg (by positivity)
    (pow_nonneg hs0 _)) (pow_nonneg (by linarith) _)

/-- This also includes the removable value at s=0. -/
theorem majorityQuotient_le_two (k : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (majorityQuotient k).eval s ≤ 2 := by
  rw [majorityQuotient_eval]
  calc
    _ ≤ ∑ i ∈ range (k + 1), 2 *
        (((2 * k).choose i : ℝ) * s ^ (2 * k - i) * (1 - s) ^ i) := by
      apply sum_le_sum
      intro i hi
      have hik : i ≤ k := by simpa using mem_range.mp hi
      have hc : ((2 * k + 1).choose i : ℝ) ≤ 2 * ((2 * k).choose i : ℝ) := by
        exact_mod_cast choose_majority_le k i hik
      have hh := mul_le_mul_of_nonneg_right hc
        (show 0 ≤ s ^ (2 * k - i) * (1 - s) ^ i from
          mul_nonneg (pow_nonneg hs0 _) (pow_nonneg (by linarith) _))
      nlinarith only [hh]
    _ = 2 * ∑ i ∈ range (k + 1),
        (((2 * k).choose i : ℝ) * s ^ (2 * k - i) * (1 - s) ^ i) := by rw [mul_sum]
    _ ≤ 2 * ∑ i ∈ range (2 * k + 1),
        (((2 * k).choose i : ℝ) * s ^ (2 * k - i) * (1 - s) ^ i) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply sum_le_sum_of_subset_of_nonneg
      · exact range_mono (by omega)
      · intro i hi hni
        exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hs0 _))
          (pow_nonneg (by linarith) _)
    _ = 2 := by rw [binomial_partition, mul_one]

end OptimalQLS.InverseSquare
