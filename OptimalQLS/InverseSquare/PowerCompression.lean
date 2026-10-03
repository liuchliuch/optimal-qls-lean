import OptimalQLS.PolynomialTransform.ChebyshevFilter
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Chebyshev compression of powers

The binomial random-walk expansion is constructed algebraically. Truncation
will retain only low-index Chebyshev polynomials; its discarded weight is
controlled by an exponential moment bound.
-/
noncomputable section
namespace OptimalQLS.InverseSquare
open Polynomial Polynomial.Chebyshev Finset

def walkPolynomial (n : ℕ) : ℝ[X] :=
  ∑ i ∈ range (n + 1), (n.choose i : ℝ[X]) * T ℝ ((n - i : ℕ) - (i : ℤ))

/-- The binomial Chebyshev expansion, proved from the three-term recurrence. -/
theorem walkPolynomial_eq (n : ℕ) : walkPolynomial n = (2 * X) ^ n := by
  induction n with
  | zero => simp [walkPolynomial]
  | succ n ih =>
    unfold walkPolynomial
    rw [show n + 1 + 1 = n + 2 by omega,
      sum_choose_succ_mul (fun i j => T ℝ ((j : ℤ) - i)) n,
      ← sum_add_distrib]
    have hterm : ∀ i ∈ range (n + 1),
        (n.choose i : ℝ[X]) * T ℝ ((n + 1 - i : ℕ) - (i : ℤ)) +
          (n.choose i : ℝ[X]) * T ℝ ((n - i : ℕ) - ((i + 1 : ℕ) : ℤ)) =
        2 * X * ((n.choose i : ℝ[X]) * T ℝ ((n - i : ℕ) - (i : ℤ))) := by
      intro i hi
      have hil : i ≤ n := by simpa using mem_range.mp hi
      have he1 : ((n + 1 - i : ℕ) : ℤ) - i = ((n - i : ℕ) : ℤ) - i + 1 := by
        omega
      have he2 : ((n - i : ℕ) : ℤ) - (i + 1 : ℕ) =
          ((n - i : ℕ) : ℤ) - i - 1 := by omega
      rw [he1, he2]
      have ht := T_add_one ℝ (((n - i : ℕ) : ℤ) - i)
      linear_combination (n.choose i : ℝ[X]) * ht
    rw [sum_congr rfl hterm, ← mul_sum]
    change 2 * X * walkPolynomial n = _
    rw [ih, pow_succ']

/-- The unnormalized random-walk identity at a real input. -/
theorem binomial_chebyshev_eval (n : ℕ) (x : ℝ) :
    (∑ i ∈ range (n + 1), (n.choose i : ℝ) *
      (T ℝ ((n : ℤ) - 2 * i)).eval x) = (2 * x) ^ n := by
  have h := congrArg (fun p : ℝ[X] => p.eval x) (walkPolynomial_eq n)
  simp only [walkPolynomial, eval_finset_sum, eval_mul, eval_natCast, eval_pow,
    eval_ofNat, eval_X] at h
  rw [← h]
  apply sum_congr rfl
  intro i hi
  have hil : i ≤ n := by simpa using mem_range.mp hi
  have he : (n : ℤ) - 2 * i = ((n - i : ℕ) : ℤ) - i := by omega
  rw [he]

/-- A quadratic argument that removes square roots from the compressed polynomial. -/
def compressionArgument : ℝ[X] := 1 - C 2 * X ^ 2

@[simp] theorem compressionArgument_eval (x : ℝ) :
    compressionArgument.eval x = 1 - 2 * x ^ 2 := by simp [compressionArgument]

/-- The full expansion of `(1-x²)^n`, before truncation. -/
theorem power_chebyshev_eval (n : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    (1 - x ^ 2) ^ n = (4 : ℝ)⁻¹ ^ n *
      ∑ i ∈ range (2 * n + 1), ((2 * n).choose i : ℝ) *
        (T ℝ ((n : ℤ) - i)).eval (1 - 2 * x ^ 2) := by
  have ht : 0 ≤ 1 - x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
  let y := Real.sqrt (1 - x ^ 2)
  have hy : y ^ 2 = 1 - x ^ 2 := Real.sq_sqrt ht
  have h := binomial_chebyshev_eval (2 * n) y
  have hsum : (∑ i ∈ range (2 * n + 1), ((2 * n).choose i : ℝ) *
      (T ℝ (((2 * n : ℕ) : ℤ) - 2 * i)).eval y) =
      ∑ i ∈ range (2 * n + 1), ((2 * n).choose i : ℝ) *
        (T ℝ ((n : ℤ) - i)).eval (1 - 2 * x ^ 2) := by
    apply sum_congr rfl
    intro i hi
    congr 1
    have hi : (((2 * n : ℕ) : ℤ) - 2 * i) = ((n : ℤ) - i) * 2 := by omega
    rw [hi, T_mul, eval_comp, T_two]
    simp only [eval_sub, eval_mul, eval_ofNat, eval_pow, eval_X, eval_one]
    congr 1
    nlinarith [hy]
  rw [hsum] at h
  rw [h]
  have hp : (2 * y) ^ (2 * n) = (4 : ℝ) ^ n * (1 - x ^ 2) ^ n := by
    rw [mul_pow, pow_mul, pow_mul, hy]
    norm_num
  rw [hp, ← mul_assoc, ← mul_pow]
  norm_num

/-- Exponential moment of the centered binomial coefficients. -/
theorem binomial_moment (n : ℕ) (t : ℝ) :
    (4 : ℝ)⁻¹ ^ n * (∑ i ∈ range (2 * n + 1), ((2 * n).choose i : ℝ) *
      Real.exp (t * ((n : ℝ) - i))) = Real.cosh (t / 2) ^ (2 * n) := by
  have h := add_pow (Real.exp (-(t / 2))) (Real.exp (t / 2)) (2 * n)
  have he : ∀ i ∈ range (2 * n + 1),
      Real.exp (-(t / 2)) ^ i * Real.exp (t / 2) ^ (2 * n - i) *
        ((2 * n).choose i : ℝ) =
      ((2 * n).choose i : ℝ) * Real.exp (t * ((n : ℝ) - i)) := by
    intro i hi
    have hil : i ≤ 2 * n := by simpa using mem_range.mp hi
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    have hh : (i : ℝ) * -(t / 2) + (2 * n - i : ℕ) * (t / 2) =
        t * ((n : ℝ) - i) := by
      rw [Nat.cast_sub hil]
      push_cast
      ring
    rw [hh]
    ring
  rw [sum_congr rfl he] at h
  rw [← h, Real.cosh_eq, div_pow]
  have hp : (Real.exp (-(t / 2)) + Real.exp (t / 2)) ^ (2 * n) =
      (Real.exp (t / 2) + Real.exp (-(t / 2))) ^ (2 * n) := by rw [add_comm]
  rw [hp]
  have hfour : (4 : ℝ)⁻¹ ^ n = ((2 : ℝ) ^ (2 * n))⁻¹ := by
    rw [pow_mul, inv_pow]
    norm_num
  rw [hfour]
  ring

/-- Gaussian exponential moment bound, still independent of approximation. -/
theorem binomial_moment_bound (n : ℕ) (t : ℝ) :
    (4 : ℝ)⁻¹ ^ n * (∑ i ∈ range (2 * n + 1), ((2 * n).choose i : ℝ) *
      Real.exp (t * ((n : ℝ) - i))) ≤ Real.exp ((n : ℝ) * t ^ 2 / 4) := by
  rw [binomial_moment]
  have h := pow_le_pow_left₀ (le_of_lt (Real.cosh_pos (t / 2)))
    (Real.cosh_le_exp_half_sq (t / 2)) (2 * n)
  rw [← Real.exp_nat_mul] at h
  convert h using 1
  congr 1
  push_cast
  ring

end OptimalQLS.InverseSquare
