import OptimalQLS.InverseSquare.CompressedPower

/-! # Compressing a finite weighted power expansion -/
noncomputable section
namespace OptimalQLS.InverseSquare
open Polynomial Finset

def weightedCompression {ι : Type*} (s : Finset ι) (c : ι → ℝ) (e : ι → ℕ)
    (m : ℕ) : ℝ[X] := ∑ i ∈ s, C (c i) * compressedPower (e i) m

@[simp] theorem weightedCompression_eval {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (e : ι → ℕ) (m : ℕ) (x : ℝ) :
    (weightedCompression s c e m).eval x = ∑ i ∈ s, c i * (compressedPower (e i) m).eval x := by
  simp only [weightedCompression, eval_finset_sum, eval_mul, eval_C]

theorem weightedCompression_even {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (e : ι → ℕ) (m : ℕ) :
    Function.Even (weightedCompression s c e m).eval := by
  intro x
  simp only [weightedCompression_eval, compressedPower_even (e _) m x]

theorem weightedCompression_degree {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (e : ι → ℕ) (m : ℕ) :
    (weightedCompression s c e m).natDegree ≤ 2 * m := by
  unfold weightedCompression
  apply natDegree_sum_le_of_forall_le
  intro i hi
  exact (natDegree_C_mul_le _ _).trans (compressedPower_degree _ _)

/-- Linearity and the absolute coefficient sum transfer the proved power bound. -/
theorem weightedCompression_error {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (e : ι → ℕ) (m N : ℕ) {B t x : ℝ}
    (he : ∀ i ∈ s, e i ≤ N) (hw : (∑ i ∈ s, |c i|) ≤ B)
    (ht : 0 ≤ t) (hx : |x| ≤ 1) :
    |(weightedCompression s c e m).eval x - ∑ i ∈ s, c i * (1 - x ^ 2) ^ e i| ≤
      B * (2 * Real.exp ((N : ℝ) * t ^ 2 / 4 - t * m)) := by
  rw [weightedCompression_eval, ← sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ s, |c i * (compressedPower (e i) m).eval x - c i * (1 - x ^ 2) ^ e i| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, |c i| * (2 * Real.exp ((N : ℝ) * t ^ 2 / 4 - t * m)) := by
      apply sum_le_sum
      intro i hi
      rw [← mul_sub, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply (compressedPower_error (e i) m ht hx).trans
      gcongr
      exact_mod_cast he i hi
    _ = (∑ i ∈ s, |c i|) * (2 * Real.exp ((N : ℝ) * t ^ 2 / 4 - t * m)) := by
      rw [sum_mul]
    _ ≤ B * (2 * Real.exp ((N : ℝ) * t ^ 2 / 4 - t * m)) :=
      mul_le_mul_of_nonneg_right hw (by positivity)

end OptimalQLS.InverseSquare
