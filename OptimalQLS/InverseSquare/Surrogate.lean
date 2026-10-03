import OptimalQLS.InverseSquare.Majority
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# A bounded algebraic inverse-square surrogate

This explicit polynomial has exponential accuracy in its majority order.
Its uncompressed degree is quadratic in the inverse spectral gap; the final
optimal result additionally requires the separate Chebyshev compression.
-/
noncomputable section
namespace OptimalQLS.InverseSquare
open Polynomial Finset

def surrogateBase (δ : ℝ) (M k : ℕ) : ℝ[X] :=
  C (δ ^ 2 / 2) * (∑ j ∈ range M, X ^ j) *
    (majorityQuotient k).comp (1 - X ^ M)

def surrogate (δ : ℝ) (M k : ℕ) : ℝ[X] :=
  (surrogateBase δ M k).comp (1 - X ^ 2)

@[simp] theorem surrogateBase_eval (δ y : ℝ) (M k : ℕ) :
    (surrogateBase δ M k).eval y =
      δ ^ 2 / 2 * (∑ j ∈ range M, y ^ j) *
        (majorityQuotient k).eval (1 - y ^ M) := by
  simp [surrogateBase]

@[simp] theorem surrogate_eval (δ x : ℝ) (M k : ℕ) :
    (surrogate δ M k).eval x =
      δ ^ 2 / 2 * (∑ j ∈ range M, (1 - x ^ 2) ^ j) *
        (majorityQuotient k).eval (1 - (1 - x ^ 2) ^ M) := by
  simp [surrogate]

theorem surrogate_even (δ : ℝ) (M k : ℕ) :
    Function.Even (surrogate δ M k).eval := by
  intro x
  simp only [surrogate_eval, neg_sq]

theorem majorityQuotient_degree (k : ℕ) : (majorityQuotient k).natDegree ≤ 2 * k := by
  unfold majorityQuotient
  apply natDegree_sum_le_of_forall_le
  intro i hi
  have hik : i ≤ k := by simpa using mem_range.mp hi
  apply natDegree_mul_le.trans
  apply (Nat.add_le_add (natDegree_C_mul_le _ _) (natDegree_pow_le)).trans
  have hd : (1 - (X : ℝ[X])).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (max_le (by simp) (by simp))
  rw [natDegree_X_pow]
  calc
    2 * k - i + i * (1 - (X : ℝ[X])).natDegree ≤ 2 * k - i + 1 * i := by nlinarith
    _ = 2 * k := by omega

theorem surrogateBase_degree (δ : ℝ) (M k : ℕ) :
    (surrogateBase δ M k).natDegree ≤ M * (2 * k + 1) := by
  have hg : (∑ j ∈ range M, (X : ℝ[X]) ^ j).natDegree ≤ M := by
    apply natDegree_sum_le_of_forall_le
    intro j hj
    simp only [natDegree_X_pow]
    exact le_of_lt (mem_range.mp hj)
  have hs : (1 - (X : ℝ[X]) ^ M).natDegree ≤ M :=
    (natDegree_sub_le _ _).trans (max_le (by simp) (by simp))
  unfold surrogateBase
  apply natDegree_mul_le.trans
  apply (Nat.add_le_add ((natDegree_C_mul_le _ _).trans hg) (natDegree_comp_le)).trans
  have hh := Nat.mul_le_mul (majorityQuotient_degree k) hs
  nlinarith

theorem surrogate_degree (δ : ℝ) (M k : ℕ) :
    (surrogate δ M k).natDegree ≤ 2 * M * (2 * k + 1) := by
  unfold surrogate
  apply natDegree_comp_le.trans
  have hs : (1 - (X : ℝ[X]) ^ 2).natDegree ≤ 2 :=
    (natDegree_sub_le _ _).trans (max_le (by simp) (by simp))
  have hh := Nat.mul_le_mul (surrogateBase_degree δ M k) hs
  nlinarith

theorem surrogate_nonneg {δ x : ℝ} (M k : ℕ) (hx : |x| ≤ 1) :
    0 ≤ (surrogate δ M k).eval x := by
  have ht0 : 0 ≤ 1 - x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
  have ht1 : 1 - x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
  have hs0 : 0 ≤ 1 - (1 - x ^ 2) ^ M := sub_nonneg.mpr (pow_le_one₀ ht0 ht1)
  have hs1 : 1 - (1 - x ^ 2) ^ M ≤ 1 := by linarith [pow_nonneg ht0 M]
  rw [surrogate_eval]
  exact mul_nonneg (mul_nonneg (by positivity) (sum_nonneg fun _ _ => pow_nonneg ht0 _))
    (majorityQuotient_nonneg k hs0 hs1)

/-- A global bound valid even at the removable singularity x=0. -/
theorem surrogate_le {δ x : ℝ} (M k : ℕ) (hx : |x| ≤ 1) :
    (surrogate δ M k).eval x ≤ δ ^ 2 * M := by
  have ht0 : 0 ≤ 1 - x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
  have ht1 : 1 - x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
  have hs0 : 0 ≤ 1 - (1 - x ^ 2) ^ M := sub_nonneg.mpr (pow_le_one₀ ht0 ht1)
  have hs1 : 1 - (1 - x ^ 2) ^ M ≤ 1 := by linarith [pow_nonneg ht0 M]
  have hg : (∑ j ∈ range M, (1 - x ^ 2) ^ j) ≤ (M : ℝ) := by
    calc
      _ ≤ ∑ j ∈ range M, (1 : ℝ) := sum_le_sum fun _ _ => pow_le_one₀ ht0 ht1
      _ = M := by simp
  have hq := majorityQuotient_le_two k hs0 hs1
  rw [surrogate_eval]
  calc
    _ ≤ δ ^ 2 / 2 * M * 2 := by
      apply mul_le_mul _ hq (majorityQuotient_nonneg k hs0 hs1) (by positivity)
      exact mul_le_mul_of_nonneg_left hg (by positivity)
    _ = δ ^ 2 * M := by ring

/-- Exact algebraic identity identifying the approximated rational function. -/
theorem surrogate_mul_sq (δ x : ℝ) (M k : ℕ) :
    (surrogate δ M k).eval x * x ^ 2 =
      δ ^ 2 / 2 * (majority k).eval (1 - (1 - x ^ 2) ^ M) := by
  rw [surrogate_eval, majority_factor, eval_mul, eval_X]
  have hg := geom_sum_mul_neg (1 - x ^ 2) M
  have heq : 1 - (1 - x ^ 2) = x ^ 2 := by ring
  rw [heq] at hg
  nlinarith only [congrArg (fun a : ℝ =>
    δ ^ 2 / 2 * a * (majorityQuotient k).eval (1 - (1 - x ^ 2) ^ M)) hg]

end OptimalQLS.InverseSquare
