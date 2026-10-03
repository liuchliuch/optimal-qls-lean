import OptimalQLS.InverseSquare.PowerCompression

/-! # An elementary exponential-moment tail bound -/
noncomputable section
namespace OptimalQLS.InverseSquare
open Polynomial Polynomial.Chebyshev Finset

def binomialWeight (n i : ℕ) : ℝ := (4 : ℝ)⁻¹ ^ n * ((2 * n).choose i : ℝ)

theorem binomialWeight_nonneg (n i : ℕ) : 0 ≤ binomialWeight n i := by
  unfold binomialWeight
  positivity

theorem weighted_moment_bound (n : ℕ) (t : ℝ) :
    (∑ i ∈ range (2 * n + 1), binomialWeight n i *
      Real.exp (t * ((n : ℝ) - i))) ≤ Real.exp ((n : ℝ) * t ^ 2 / 4) := by
  simpa only [binomialWeight, mul_assoc, ← mul_sum] using binomial_moment_bound n t

/-- Exponentiating an absolute-value cutoff costs two exponential moments. -/
theorem exponential_cutoff {r a t : ℝ} (ht : 0 ≤ t) (ha : a ≤ |r|) :
    1 ≤ Real.exp (-(t * a)) * (Real.exp (t * r) + Real.exp (-(t * r))) := by
  have he : Real.exp (t * a) ≤ Real.exp (t * r) + Real.exp (-(t * r)) := by
    by_cases hr : 0 ≤ r
    · rw [abs_of_nonneg hr] at ha
      have h := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ha ht)
      linarith [Real.exp_pos (-(t * r))]
    · rw [abs_of_neg (lt_of_not_ge hr)] at ha
      have h := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ha ht)
      rw [mul_neg] at h
      linarith [Real.exp_pos (t * r)]
  have hh := mul_le_mul_of_nonneg_left he (le_of_lt (Real.exp_pos (-(t * a))))
  have heq : Real.exp (-(t * a)) * Real.exp (t * a) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [heq] at hh
  exact hh

/-- A centered binomial tail, uniformly valid also at n=0. -/
theorem binomial_tail_bound (n m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (∑ i ∈ (range (2 * n + 1)).filter (fun i : ℕ => (m : ℤ) < |(n : ℤ) - (i : ℤ)|),
      binomialWeight n i) ≤
      2 * Real.exp ((n : ℝ) * t ^ 2 / 4 - t * m) := by
  let s := (range (2 * n + 1)).filter (fun i : ℕ => (m : ℤ) < |(n : ℤ) - (i : ℤ)|)
  have hterm : ∀ i ∈ s, binomialWeight n i ≤
      Real.exp (-(t * m)) * (binomialWeight n i *
        (Real.exp (t * ((n : ℝ) - i)) + Real.exp (-(t * ((n : ℝ) - i))))) := by
    intro i hi
    have hi' : (m : ℤ) < |(n : ℤ) - i| := (mem_filter.mp hi).2
    have hreal : (m : ℝ) ≤ |(n : ℝ) - i| := by exact_mod_cast le_of_lt hi'
    have h := mul_le_mul_of_nonneg_left (exponential_cutoff ht hreal)
      (binomialWeight_nonneg n i)
    nlinarith only [h]
  have hfull : (∑ i ∈ s, binomialWeight n i *
      (Real.exp (t * ((n : ℝ) - i)) + Real.exp (-(t * ((n : ℝ) - i))))) ≤
      (∑ i ∈ range (2 * n + 1), binomialWeight n i *
        (Real.exp (t * ((n : ℝ) - i)) + Real.exp (-(t * ((n : ℝ) - i))))) := by
    apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    intro i hi hni
    exact mul_nonneg (binomialWeight_nonneg _ _) (by positivity)
  have hm1 := weighted_moment_bound n t
  have hm2 := weighted_moment_bound n (-t)
  have hm : (∑ i ∈ range (2 * n + 1), binomialWeight n i *
      (Real.exp (t * ((n : ℝ) - i)) + Real.exp (-(t * ((n : ℝ) - i))))) ≤
      2 * Real.exp ((n : ℝ) * t ^ 2 / 4) := by
    simp_rw [mul_add, sum_add_distrib]
    simp only [neg_mul, neg_sq] at hm2
    linarith
  calc
    _ ≤ ∑ i ∈ s, Real.exp (-(t * m)) * (binomialWeight n i *
        (Real.exp (t * ((n : ℝ) - i)) + Real.exp (-(t * ((n : ℝ) - i))))) :=
      sum_le_sum hterm
    _ = Real.exp (-(t * m)) * ∑ i ∈ s, binomialWeight n i *
        (Real.exp (t * ((n : ℝ) - i)) + Real.exp (-(t * ((n : ℝ) - i)))) := by
      rw [mul_sum]
    _ ≤ Real.exp (-(t * m)) * (2 * Real.exp ((n : ℝ) * t ^ 2 / 4)) :=
      mul_le_mul_of_nonneg_left (hfull.trans hm) (by positivity)
    _ = 2 * Real.exp ((n : ℝ) * t ^ 2 / 4 - t * m) := by
      rw [show Real.exp (-(t * m)) * (2 * Real.exp ((n : ℝ) * t ^ 2 / 4)) =
        2 * (Real.exp (-(t * m)) * Real.exp ((n : ℝ) * t ^ 2 / 4)) by ring,
        ← Real.exp_add]
      congr 2
      ring

end OptimalQLS.InverseSquare
