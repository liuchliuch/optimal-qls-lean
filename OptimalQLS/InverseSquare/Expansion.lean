import OptimalQLS.InverseSquare.Parameters
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! # Small-weight power expansion of the bounded surrogate -/
noncomputable section
namespace OptimalQLS.InverseSquare
open Polynomial Finset

abbrev ExpansionIndex := Σ _ : ℕ, ℕ × ℕ

def expansionIndices (M k : ℕ) : Finset ExpansionIndex :=
  (range (k + 1)).sigma fun i => (range (2 * k - i + 1)) ×ˢ (range M)

def expansionCoefficient (δ : ℝ) (k : ℕ) (a : ExpansionIndex) : ℝ :=
  δ ^ 2 / 2 * ((2 * k + 1).choose a.1 : ℝ) *
    ((2 * k - a.1).choose a.2.1 : ℝ) * (-1) ^ a.2.1

def expansionExponent (M : ℕ) (a : ExpansionIndex) : ℕ :=
  a.2.2 + M * (a.1 + a.2.1)

theorem expansionExponent_le {M k : ℕ} {a : ExpansionIndex}
    (ha : a ∈ expansionIndices M k) : expansionExponent M a ≤ M * (2 * k + 1) := by
  obtain ⟨hi, hrest⟩ := mem_sigma.mp ha
  obtain ⟨hl, hj⟩ := mem_product.mp hrest
  have hi' : a.1 ≤ k := by simpa using mem_range.mp hi
  have hl' : a.2.1 ≤ 2 * k - a.1 := by simpa using mem_range.mp hl
  have hj' : a.2.2 < M := mem_range.mp hj
  have hi2 : a.1 + a.2.1 ≤ 2 * k := by omega
  have hm := Nat.mul_le_mul_left M hi2
  unfold expansionExponent
  nlinarith

/-- The only power-series manipulation is a finite binomial identity. -/
theorem finite_signed_power (r M : ℕ) (y : ℝ) :
    (1 - y ^ M) ^ r = ∑ l ∈ range (r + 1),
      (r.choose l : ℝ) * (-1) ^ l * y ^ (M * l) := by
  have h := add_pow (-(y ^ M)) (1 : ℝ) r
  have he : -(y ^ M) + 1 = 1 - y ^ M := by ring
  rw [he] at h
  rw [h]
  apply sum_congr rfl
  intro l hl
  rw [neg_pow, ← pow_mul]
  simp only [one_pow, mul_one]
  ring

/-- An exact finite expansion with weights independent of inverse-gap growth. -/
theorem surrogate_expansion (δ x : ℝ) (M k : ℕ) :
    (surrogate δ M k).eval x =
      ∑ a ∈ expansionIndices M k, expansionCoefficient δ k a *
        (1 - x ^ 2) ^ expansionExponent M a := by
  rw [surrogate_eval, majorityQuotient_eval]
  have he : 1 - (1 - (1 - x ^ 2) ^ M) = (1 - x ^ 2) ^ M := by ring
  rw [he]
  simp only [expansionIndices, sum_sigma, sum_product, expansionCoefficient,
    expansionExponent]
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [finite_signed_power, ← pow_mul]
  simp only [mul_sum, sum_mul]
  apply sum_congr rfl
  intro l hl
  apply sum_congr rfl
  intro j hj
  rw [Nat.mul_add, pow_add, pow_add]
  ring

theorem expansionCoefficient_abs (δ : ℝ) (k : ℕ) (a : ExpansionIndex) :
    |expansionCoefficient δ k a| = δ ^ 2 / 2 * ((2 * k + 1).choose a.1 : ℝ) *
      ((2 * k - a.1).choose a.2.1 : ℝ) := by
  unfold expansionCoefficient
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
    abs_of_nonneg (by positivity)]

theorem expansionWeight_eq (δ : ℝ) (M k : ℕ) :
    (∑ a ∈ expansionIndices M k, |expansionCoefficient δ k a|) =
      (δ ^ 2 / 2 * M) * ∑ i ∈ range (k + 1),
        ((2 * k + 1).choose i : ℝ) * (2 : ℝ) ^ (2 * k - i) := by
  simp only [expansionCoefficient_abs, expansionIndices, sum_sigma, sum_product]
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  simp only [sum_const, card_range, nsmul_eq_mul]
  calc
    _ = (δ ^ 2 / 2 * M * ((2 * k + 1).choose i : ℝ)) *
        ∑ l ∈ range (2 * k - i + 1), ((2 * k - i).choose l : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro l hl
      ring
    _ = _ := by
      have h : (∑ l ∈ range (2 * k - i + 1), ((2 * k - i).choose l : ℝ)) =
          (2 : ℝ) ^ (2 * k - i) := by exact_mod_cast Nat.sum_range_choose (2 * k - i)
      rw [h]
      ring

theorem choose_power_sum_bound (k : ℕ) :
    (∑ i ∈ range (k + 1), ((2 * k + 1).choose i : ℝ) * (2 : ℝ) ^ (2 * k - i)) ≤
      (3 : ℝ) ^ (2 * k + 1) := by
  calc
    _ ≤ ∑ i ∈ range (k + 1), ((2 * k + 1).choose i : ℝ) *
        (2 : ℝ) ^ (2 * k + 1 - i) := by
      apply sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    _ ≤ ∑ i ∈ range (2 * k + 1 + 1), ((2 * k + 1).choose i : ℝ) *
        (2 : ℝ) ^ (2 * k + 1 - i) := by
      apply sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
      intro i hi hni
      positivity
    _ = (3 : ℝ) ^ (2 * k + 1) := by
      have h := add_pow (1 : ℝ) 2 (2 * k + 1)
      norm_num only [one_pow] at h
      convert h.symm using 1
      · apply sum_congr rfl
        intro i hi
        ring

/-- The expansion weight is exponential only in majority order, never in M. -/
theorem expansionWeight_bound {δ : ℝ} {M : ℕ} (k : ℕ)
    (hM : δ ^ 2 * (M : ℝ) ≤ 1) :
    (∑ a ∈ expansionIndices M k, |expansionCoefficient δ k a|) ≤
      (3 : ℝ) ^ (2 * k + 1) := by
  rw [expansionWeight_eq]
  calc
    _ ≤ (δ ^ 2 / 2 * M) * (3 : ℝ) ^ (2 * k + 1) :=
      mul_le_mul_of_nonneg_left (choose_power_sum_bound k) (by positivity)
    _ ≤ (3 : ℝ) ^ (2 * k + 1) :=
      mul_le_of_le_one_left (by positivity) (by nlinarith)

end OptimalQLS.InverseSquare
