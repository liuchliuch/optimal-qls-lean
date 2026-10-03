import OptimalQLS.InverseSquare.PowerTail

/-! # Constructive low-degree approximation of `(1-x²)^n` -/
noncomputable section
namespace OptimalQLS.InverseSquare
open Polynomial Polynomial.Chebyshev Finset

def compressedPower (n m : ℕ) : ℝ[X] :=
  ∑ i ∈ (range (2 * n + 1)).filter
    (fun i : ℕ => |(n : ℤ) - (i : ℤ)| ≤ (m : ℤ)),
    C (binomialWeight n i) * (T ℝ ((n : ℤ) - i)).comp compressionArgument

@[simp] theorem compressedPower_eval (n m : ℕ) (x : ℝ) :
    (compressedPower n m).eval x =
      ∑ i ∈ (range (2 * n + 1)).filter
        (fun i : ℕ => |(n : ℤ) - (i : ℤ)| ≤ (m : ℤ)),
      binomialWeight n i * (T ℝ ((n : ℤ) - i)).eval (1 - 2 * x ^ 2) := by
  simp only [compressedPower, eval_finset_sum, eval_mul, eval_C, eval_comp,
    compressionArgument_eval]

theorem compressedPower_even (n m : ℕ) : Function.Even (compressedPower n m).eval := by
  intro x
  simp only [compressedPower_eval, neg_sq]

theorem compressionArgument_degree : compressionArgument.natDegree ≤ 2 := by
  unfold compressionArgument
  apply (natDegree_sub_le _ _).trans
  apply max_le (by simp)
  exact (natDegree_C_mul_le _ _).trans (by simp)

/-- The approximation degree depends on the truncation, not the original power. -/
theorem compressedPower_degree (n m : ℕ) : (compressedPower n m).natDegree ≤ 2 * m := by
  unfold compressedPower
  apply natDegree_sum_le_of_forall_le
  intro i hi
  have hiabs := (mem_filter.mp hi).2
  have hdeg : ((n : ℤ) - i).natAbs ≤ m := by
    rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
    exact hiabs
  apply (natDegree_C_mul_le _ _).trans
  apply natDegree_comp_le.trans
  rw [natDegree_T]
  have h := Nat.mul_le_mul hdeg compressionArgument_degree
  omega

/-- Actual approximation with a Gaussian moment bound, no certificate premises. -/
theorem compressedPower_error (n m : ℕ) {t x : ℝ} (ht : 0 ≤ t) (hx : |x| ≤ 1) :
    |(compressedPower n m).eval x - (1 - x ^ 2) ^ n| ≤
      2 * Real.exp ((n : ℝ) * t ^ 2 / 4 - t * m) := by
  let f : ℕ → ℝ := fun i => binomialWeight n i *
    (T ℝ ((n : ℤ) - i)).eval (1 - 2 * x ^ 2)
  let s := range (2 * n + 1)
  let good : ℕ → Prop := fun i => |(n : ℤ) - (i : ℤ)| ≤ (m : ℤ)
  have hfull : (1 - x ^ 2) ^ n = ∑ i ∈ s, f i := by
    rw [power_chebyshev_eval n hx, mul_sum]
    apply sum_congr rfl
    intro i hi
    simp only [f, binomialWeight]
    ring
  have hsplit := sum_filter_add_sum_filter_not s good f
  have hbad : (1 - x ^ 2) ^ n - (compressedPower n m).eval x =
      ∑ i ∈ s.filter (fun i => ¬ good i), f i := by
    rw [hfull, compressedPower_eval]
    change (∑ i ∈ s, f i) - (∑ i ∈ s.filter good, f i) = _
    linarith
  rw [abs_sub_comm, hbad]
  have harg : |1 - 2 * x ^ 2| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_abs x, abs_nonneg x, sq_nonneg x]
  calc
    _ ≤ ∑ i ∈ s.filter (fun i => ¬ good i), |f i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s.filter (fun i => ¬ good i), binomialWeight n i := by
      apply sum_le_sum
      intro i hi
      dsimp [f]
      rw [abs_mul, abs_of_nonneg (binomialWeight_nonneg _ _)]
      exact mul_le_of_le_one_right (binomialWeight_nonneg _ _)
        (OptimalQLS.PolynomialTransform.abs_eval_T_real_le_one _ harg)
    _ ≤ 2 * Real.exp ((n : ℝ) * t ^ 2 / 4 - t * m) := by
      simpa only [s, good, not_le] using binomial_tail_bound n m ht

end OptimalQLS.InverseSquare
