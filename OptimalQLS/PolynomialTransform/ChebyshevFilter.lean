import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Explicit normalized Chebyshev kernel filter

The polynomial is constructed from mathlib's Chebyshev polynomials, rather
than postulated through an approximation certificate. The scalar estimates
in this file are independent of quantum signal processing.
-/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Polynomial
open Polynomial.Chebyshev

/-- Elementary oscillatory bound, proved here to avoid importing the roots theory. -/
theorem abs_eval_T_real_le_one (n : ℤ) {x : ℝ} (hx : |x| ≤ 1) :
    |(T ℝ n).eval x| ≤ 1 := by
  rw [← Real.cos_arccos (neg_le_of_abs_le hx) (le_of_abs_le hx), T_real_cos]
  exact Real.abs_cos_le_one _

theorem one_le_eval_T_real (n : ℤ) {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ (T ℝ n).eval x := by
  rw [← Real.cosh_arcosh hx, T_real_cosh]
  exact Real.one_le_cosh _

theorem one_le_abs_eval_T_real (n : ℤ) {x : ℝ} (hx : 1 ≤ |x|) :
    1 ≤ |(T ℝ n).eval x| := by
  by_cases hxp : 0 ≤ x
  · exact (one_le_eval_T_real n (by simpa [abs_of_nonneg hxp] using hx)).trans
      (le_abs_self _)
  · have hn : 1 ≤ -x := by simpa [abs_of_neg (lt_of_not_ge hxp)] using hx
    have ht := one_le_eval_T_real n hn
    rw [T_eval_neg] at ht
    calc
      1 ≤ |(n.negOnePow : ℝ) * (T ℝ n).eval x| := ht.trans (le_abs_self _)
      _ = |(T ℝ n).eval x| := by rw [abs_mul, abs_unit_intCast, one_mul]

/-- The quadratic change of variable in the Lin--Tong filter. -/
def filterArgument (δ : ℝ) : ℝ[X] :=
  -1 + C (2 / (1 - δ ^ 2)) * (X ^ 2 - C (δ ^ 2))

/-- The value of the argument at zero, with its sign removed. -/
def filterEndpoint (δ : ℝ) : ℝ := (1 + δ ^ 2) / (1 - δ ^ 2)

/-- A concrete real polynomial, including its normalization. -/
def chebyshevFilter (δ : ℝ) (ell : ℕ) : ℝ[X] :=
  C (((T ℝ (ell : ℤ)).eval (-filterEndpoint δ))⁻¹) *
    (T ℝ (ell : ℤ)).comp (filterArgument δ)

@[simp] theorem filterArgument_eval (δ x : ℝ) :
    (filterArgument δ).eval x = -1 + 2 * (x ^ 2 - δ ^ 2) / (1 - δ ^ 2) := by
  simp [filterArgument]
  ring

@[simp] theorem chebyshevFilter_eval (δ : ℝ) (ell : ℕ) (x : ℝ) :
    (chebyshevFilter δ ell).eval x =
      (T ℝ (ell : ℤ)).eval (-1 + 2 * (x ^ 2 - δ ^ 2) / (1 - δ ^ 2)) /
        (T ℝ (ell : ℤ)).eval (-filterEndpoint δ) := by
  simp [chebyshevFilter, div_eq_mul_inv, mul_comm]

theorem filterArgument_zero {δ : ℝ} (hδ : δ ^ 2 < 1) :
    (filterArgument δ).eval 0 = -filterEndpoint δ := by
  rw [filterArgument_eval]
  unfold filterEndpoint
  field_simp [show 1 - δ ^ 2 ≠ 0 by linarith]
  ring

theorem filterEndpoint_ge_one {δ : ℝ} (hδ : δ ^ 2 < 1) :
    1 ≤ filterEndpoint δ := by
  rw [filterEndpoint, le_div_iff₀ (by linarith)]
  nlinarith [sq_nonneg δ]

theorem filter_denominator_abs_ge_one {δ : ℝ} (hδ : δ ^ 2 < 1) (ell : ℕ) :
    1 ≤ |(T ℝ (ell : ℤ)).eval (-filterEndpoint δ)| := by
  apply one_le_abs_eval_T_real
  rw [abs_neg, abs_of_nonneg (by linarith [filterEndpoint_ge_one hδ])]
  exact filterEndpoint_ge_one hδ

theorem filter_denominator_ne_zero {δ : ℝ} (hδ : δ ^ 2 < 1) (ell : ℕ) :
    (T ℝ (ell : ℤ)).eval (-filterEndpoint δ) ≠ 0 := by
  have := filter_denominator_abs_ge_one hδ ell
  intro hz
  rw [hz, abs_zero] at this
  linarith

/-- Exact normalization, without an approximation hypothesis. -/
@[simp] theorem chebyshevFilter_zero {δ : ℝ} (hδ : δ ^ 2 < 1) (ell : ℕ) :
    (chebyshevFilter δ ell).eval 0 = 1 := by
  simp only [chebyshevFilter, eval_mul, eval_C, eval_comp]
  rw [filterArgument_zero hδ]
  exact inv_mul_cancel₀ (filter_denominator_ne_zero hδ ell)

/-- Evenness follows from the literal quadratic composition. -/
theorem chebyshevFilter_even (δ : ℝ) (ell : ℕ) :
    Function.Even (chebyshevFilter δ ell).eval := by
  intro x
  simp only [chebyshevFilter_eval, neg_sq]

/-- Exact algebraic degree of the filter argument. -/
theorem filterArgument_natDegree {δ : ℝ} (hδ : δ ^ 2 < 1) :
    (filterArgument δ).natDegree = 2 := by
  have h : filterArgument δ = C (2 / (1 - δ ^ 2)) * X ^ 2 +
      C (-1 - 2 * δ ^ 2 / (1 - δ ^ 2)) := by
    have heq : -1 - 2 * δ ^ 2 / (1 - δ ^ 2) =
        -1 - (2 / (1 - δ ^ 2)) * δ ^ 2 := by ring
    rw [heq]
    simp only [filterArgument, map_sub, map_neg, map_one, map_mul]
    ring
  rw [h]
  have hc : 2 / (1 - δ ^ 2) ≠ 0 := div_ne_zero (by norm_num) (by linarith)
  rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_C_mul hc, natDegree_X_pow]
  rw [natDegree_C_mul hc, natDegree_X_pow, natDegree_C]
  norm_num

/-- Exact degree, including the degree-zero case. -/
theorem chebyshevFilter_natDegree {δ : ℝ} (hδ : δ ^ 2 < 1) (ell : ℕ) :
    (chebyshevFilter δ ell).natDegree = 2 * ell := by
  rw [chebyshevFilter, natDegree_C_mul (inv_ne_zero (filter_denominator_ne_zero hδ ell)),
    natDegree_comp, natDegree_T, filterArgument_natDegree hδ]
  simp [Nat.mul_comm]

/-- Monotonicity outside the oscillatory interval. -/
theorem chebyshev_eval_mono {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) (ell : ℕ) :
    (T ℝ (ell : ℤ)).eval x ≤ (T ℝ (ell : ℤ)).eval y := by
  have hy : 1 ≤ y := hx.trans hxy
  conv_lhs => rw [← Real.cosh_arcosh hx]
  conv_rhs => rw [← Real.cosh_arcosh hy]
  rw [T_real_cosh, T_real_cosh]
  apply Real.cosh_le_cosh.mpr
  rw [abs_of_nonneg (mul_nonneg (by positivity) (Real.arcosh_nonneg hx)),
    abs_of_nonneg (mul_nonneg (by positivity) (Real.arcosh_nonneg hy))]
  exact mul_le_mul_of_nonneg_left
    ((Real.arcosh_le_arcosh (by linarith) (by linarith)).mpr hxy) (by positivity)

theorem abs_chebyshev_eval_neg (ell : ℕ) (x : ℝ) :
    |(T ℝ (ell : ℤ)).eval (-x)| = |(T ℝ (ell : ℤ)).eval x| := by
  rw [T_eval_neg, abs_mul, abs_unit_intCast, one_mul]

/-- A bound on the whole interval, including the part inside the spectral gap. -/
theorem chebyshev_envelope {b x : ℝ} (hb : 1 ≤ b) (hx : |x| ≤ b) (ell : ℕ) :
    |(T ℝ (ell : ℤ)).eval x| ≤ (T ℝ (ell : ℤ)).eval b := by
  by_cases hx1 : |x| ≤ 1
  · exact (abs_eval_T_real_le_one _ hx1).trans (one_le_eval_T_real _ hb)
  have hxa : 1 ≤ |x| := le_of_lt (lt_of_not_ge hx1)
  have ha : |(T ℝ (ell : ℤ)).eval x| = (T ℝ (ell : ℤ)).eval |x| := by
    by_cases hxp : 0 ≤ x
    · rw [abs_of_nonneg hxp, abs_of_nonneg (by linarith [one_le_eval_T_real (ell : ℤ) (by simpa [abs_of_nonneg hxp] using hxa)])]
    · rw [abs_of_neg (lt_of_not_ge hxp)]
      rw [← abs_chebyshev_eval_neg ell x]
      exact abs_of_nonneg (by linarith [one_le_eval_T_real (ell : ℤ) (by simpa [abs_of_neg (lt_of_not_ge hxp)] using hxa)])
  rw [ha]
  exact chebyshev_eval_mono hxa hx ell

theorem filterArgument_bound {δ x : ℝ} (hδ : δ ^ 2 < 1) (hx : |x| ≤ 1) :
    |(filterArgument δ).eval x| ≤ filterEndpoint δ := by
  have hd : 0 < 1 - δ ^ 2 := by linarith
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
  have heq : (filterArgument δ).eval x = (2 * x ^ 2 - 1 - δ ^ 2) / (1 - δ ^ 2) := by
    rw [filterArgument_eval]
    field_simp
    ring
  rw [heq, abs_le, filterEndpoint, ← neg_div]
  constructor
  · exact (div_le_div_iff_of_pos_right hd).mpr (by nlinarith [sq_nonneg x])
  · exact (div_le_div_iff_of_pos_right hd).mpr (by nlinarith [sq_nonneg δ])

/-- Uniform bound one on the complete signal interval. -/
theorem chebyshevFilter_bounded {δ x : ℝ} (hδ : δ ^ 2 < 1) (ell : ℕ)
    (hx : |x| ≤ 1) : |(chebyshevFilter δ ell).eval x| ≤ 1 := by
  have hd := filter_denominator_abs_ge_one hδ ell
  rw [chebyshevFilter_eval, abs_div]
  apply (div_le_one (by linarith : 0 < |(T ℝ (ell : ℤ)).eval (-filterEndpoint δ)|)).mpr
  have heval : 0 ≤ (T ℝ (ell : ℤ)).eval (filterEndpoint δ) :=
    le_trans (by norm_num) (one_le_eval_T_real (ell : ℤ) (filterEndpoint_ge_one hδ))
  rw [abs_chebyshev_eval_neg, abs_of_nonneg heval]
  simpa only [filterArgument_eval] using
    chebyshev_envelope (filterEndpoint_ge_one hδ) (filterArgument_bound hδ hx) ell

/-- Positive hyperbolic parameter of the endpoint. -/
def filterRate (δ : ℝ) : ℝ := Real.log ((1 + δ) / (1 - δ))

theorem cosh_filterRate {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Real.cosh (filterRate δ) = filterEndpoint δ := by
  have hq : 0 < (1 + δ) / (1 - δ) := div_pos (by linarith) (by linarith)
  rw [filterRate, Real.cosh_eq, Real.exp_log hq, Real.exp_neg, Real.exp_log hq]
  unfold filterEndpoint
  have hm : 1 - δ ≠ 0 := by linarith
  have hp : 1 + δ ≠ 0 := by linarith
  have hs : 1 - δ ^ 2 ≠ 0 := by nlinarith
  field_simp [hm, hp, hs]
  ring

/-- A deliberately elementary lower bound suffices for the paper's constant. -/
theorem filterRate_lower {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3) :
    Real.sqrt 2 * δ ≤ filterRate δ := by
  have hd : 0 < 1 - δ := by linarith
  have hp : 0 < 1 + δ := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hp hd)
  have heq : 1 - ((1 + δ) / (1 - δ))⁻¹ = 2 * δ / (1 + δ) := by
    field_simp
    ring
  rw [heq] at hlog
  have hs : Real.sqrt 2 ≤ 3 / 2 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  calc
    Real.sqrt 2 * δ ≤ (3 / 2) * δ := mul_le_mul_of_nonneg_right hs hδ0.le
    _ ≤ 2 * δ / (1 + δ) := (le_div_iff₀ hp).mpr (by nlinarith)
    _ ≤ filterRate δ := hlog

theorem filter_denominator_cosh {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (ell : ℕ) :
    |(T ℝ (ell : ℤ)).eval (-filterEndpoint δ)| =
      Real.cosh ((ell : ℝ) * filterRate δ) := by
  rw [abs_chebyshev_eval_neg, ← cosh_filterRate hδ0 hδ1, T_real_cosh,
    abs_of_pos (Real.cosh_pos _)]
  simp

theorem filterArgument_tail {δ x : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ^ 2 < 1)
    (hx0 : δ ≤ |x|) (hx1 : |x| ≤ 1) :
    |(filterArgument δ).eval x| ≤ 1 := by
  have hd : 0 < 1 - δ ^ 2 := by linarith
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
  have hδx : δ ^ 2 ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
  rw [filterArgument_eval, abs_le]
  constructor
  · have : 0 ≤ 2 * (x ^ 2 - δ ^ 2) / (1 - δ ^ 2) :=
      div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hδx)) hd.le
    linarith
  · have : 2 * (x ^ 2 - δ ^ 2) / (1 - δ ^ 2) ≤ 2 :=
      (div_le_iff₀ hd).mpr (by nlinarith)
    linarith

/-- Explicit tail estimate before choosing the degree. -/
theorem chebyshevFilter_tail_exponential {δ x : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3) (ell : ℕ)
    (hx0 : δ ≤ |x|) (hx1 : |x| ≤ 1) :
    |(chebyshevFilter δ ell).eval x| ≤
      2 * Real.exp (-((ell : ℝ) * (Real.sqrt 2 * δ))) := by
  have hδsq : δ ^ 2 < 1 := by nlinarith
  have hδlt : δ < 1 := by linarith
  have hd : 0 < Real.cosh ((ell : ℝ) * filterRate δ) := Real.cosh_pos _
  have hn := abs_eval_T_real_le_one (ell : ℤ) (filterArgument_tail hδ0.le hδsq hx0 hx1)
  rw [chebyshevFilter_eval, abs_div, filter_denominator_cosh hδ0 hδlt]
  calc
    |(T ℝ (ell : ℤ)).eval (-1 + 2 * (x ^ 2 - δ ^ 2) / (1 - δ ^ 2))| /
        Real.cosh ((ell : ℝ) * filterRate δ) ≤ 1 / Real.cosh ((ell : ℝ) * filterRate δ) :=
      div_le_div_of_nonneg_right (by simpa only [filterArgument_eval] using hn) hd.le
    _ ≤ 2 * Real.exp (-((ell : ℝ) * filterRate δ)) := by
      apply (div_le_iff₀ hd).mpr
      rw [Real.cosh_eq, Real.exp_neg]
      have he : 0 < Real.exp ((ell : ℝ) * filterRate δ) := Real.exp_pos _
      field_simp
      nlinarith [sq_nonneg (Real.exp ((ell : ℝ) * filterRate δ))]
    _ ≤ 2 * Real.exp (-((ell : ℝ) * (Real.sqrt 2 * δ))) := by
      gcongr
      exact filterRate_lower hδ0 hδ1

/-- The exact natural-number ceiling in Lemma 5.1. -/
def filterOrder (δ η : ℝ) : ℕ :=
  ⌈Real.log (2 / η) / (Real.sqrt 2 * δ)⌉₊

/-- The polynomial requested by the paper, with no existential certificate. -/
def kernelFilter (δ η : ℝ) : ℝ[X] := chebyshevFilter δ (filterOrder δ η)

theorem filter_parameter_le_third {δ : ℝ} (hδ : δ ≤ 1 / Real.sqrt 12) : δ ≤ 1 / 3 := by
  have hs : (3 : ℝ) ≤ Real.sqrt 12 := Real.le_sqrt_of_sq_le (by norm_num)
  exact hδ.trans (one_div_le_one_div_of_le (by norm_num) hs)

/-- The quantitative tail bound of Lemma 5.1. -/
theorem kernelFilter_tail {δ η x : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / Real.sqrt 12) (hη0 : 0 < η)
    (hx0 : δ ≤ |x|) (hx1 : |x| ≤ 1) :
    |(kernelFilter δ η).eval x| ≤ η := by
  have hden : 0 < Real.sqrt 2 * δ := mul_pos (Real.sqrt_pos.2 (by norm_num)) hδ0
  have horder : Real.log (2 / η) ≤ (filterOrder δ η : ℝ) * (Real.sqrt 2 * δ) := by
    exact (div_le_iff₀ hden).mp (Nat.le_ceil _)
  calc
    |(kernelFilter δ η).eval x| ≤
        2 * Real.exp (-((filterOrder δ η : ℝ) * (Real.sqrt 2 * δ))) :=
      chebyshevFilter_tail_exponential hδ0 (filter_parameter_le_third hδ1) _ hx0 hx1
    _ ≤ 2 * Real.exp (-Real.log (2 / η)) := by gcongr
    _ = η := by rw [Real.exp_neg, Real.exp_log (div_pos (by norm_num) hη0)]; field_simp

/-- A concrete bound stronger than an unspecified big-O degree assertion. -/
theorem kernelFilter_degree_bound {δ η : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / Real.sqrt 12) (hη0 : 0 < η) (hη1 : η < 1 / 2) :
    ((kernelFilter δ η).natDegree : ℝ) <
      2 * (Real.log (2 / η) / (Real.sqrt 2 * δ) + 1) := by
  have hδthird := filter_parameter_le_third hδ1
  have hδsq : δ ^ 2 < 1 := by nlinarith
  rw [kernelFilter, chebyshevFilter_natDegree hδsq]
  push_cast
  have hlog : 0 ≤ Real.log (2 / η) := Real.log_nonneg (by
    apply (le_div_iff₀ hη0).mpr
    linarith)
  have hc := Nat.ceil_lt_add_one (div_nonneg hlog (by positivity : 0 ≤ Real.sqrt 2 * δ))
  dsimp only [filterOrder]
  linarith

/-- Uniform constant for the advertised O(δ⁻¹ log(1/η)) degree. -/
theorem kernelFilter_degree_complexity {δ η : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / Real.sqrt 12) (hη0 : 0 < η) (hη1 : η < 1 / 2) :
    ((kernelFilter δ η).natDegree : ℝ) < 6 * δ⁻¹ * Real.log (1 / η) := by
  have hδthird := filter_parameter_le_third hδ1
  have htwo : (2 : ℝ) ≤ 1 / η := (le_div_iff₀ hη0).mpr (by linarith)
  have hlower : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlogtwo : Real.log 2 ≤ Real.log (1 / η) :=
    Real.log_le_log (by norm_num) htwo
  have hL : (1 / 2 : ℝ) ≤ Real.log (1 / η) := hlower.trans hlogtwo
  have heq : Real.log (2 / η) = Real.log 2 + Real.log (1 / η) := by
    rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hη0.ne',
      Real.log_div one_ne_zero hη0.ne', Real.log_one]
    ring
  have hlog : 0 ≤ Real.log (2 / η) := by rw [heq]; linarith
  have hs : (1 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hq : Real.log (2 / η) / (Real.sqrt 2 * δ) ≤ 2 * Real.log (1 / η) / δ := by
    calc
      Real.log (2 / η) / (Real.sqrt 2 * δ) ≤ Real.log (2 / η) / δ :=
        div_le_div_of_nonneg_left hlog hδ0 (by nlinarith)
      _ ≤ 2 * Real.log (1 / η) / δ :=
        div_le_div_of_nonneg_right (by rw [heq]; linarith) hδ0.le
  rw [mul_div_assoc] at hq
  have hone : 1 ≤ Real.log (1 / η) / δ := (le_div_iff₀ hδ0).mpr (by linarith)
  calc
    ((kernelFilter δ η).natDegree : ℝ) <
        2 * (Real.log (2 / η) / (Real.sqrt 2 * δ) + 1) :=
      kernelFilter_degree_bound hδ0 hδ1 hη0 hη1
    _ ≤ 6 * (Real.log (1 / η) / δ) := by linarith
    _ = 6 * δ⁻¹ * Real.log (1 / η) := by ring

/-- The full scalar filter, with explicit degree rather than hidden constants. -/
theorem lemma51_kernel_filter {δ η : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / Real.sqrt 12) (hη0 : 0 < η) (hη1 : η < 1 / 2) :
    Function.Even (kernelFilter δ η).eval ∧
    (kernelFilter δ η).natDegree = 2 * filterOrder δ η ∧
    (kernelFilter δ η).eval 0 = 1 ∧
    (∀ x : ℝ, |x| ≤ 1 → |(kernelFilter δ η).eval x| ≤ 1) ∧
    (∀ x : ℝ, δ ≤ |x| → |x| ≤ 1 → |(kernelFilter δ η).eval x| ≤ η) ∧
    ((kernelFilter δ η).natDegree : ℝ) <
      2 * (Real.log (2 / η) / (Real.sqrt 2 * δ) + 1) := by
  have hδthird := filter_parameter_le_third hδ1
  have hδsq : δ ^ 2 < 1 := by nlinarith
  exact ⟨chebyshevFilter_even _ _, chebyshevFilter_natDegree hδsq _,
    chebyshevFilter_zero hδsq _, fun x hx => chebyshevFilter_bounded hδsq _ hx,
    fun x hx0 hx1 => kernelFilter_tail hδ0 hδ1 hη0 hx0 hx1,
    kernelFilter_degree_bound hδ0 hδ1 hη0 hη1⟩

end OptimalQLS.PolynomialTransform
