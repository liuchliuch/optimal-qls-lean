import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Scalar estimates used in the concrete Euclidean auxiliary-matrix geometry.
Here `t = κ⁻¹`. No operator conclusions are assumed. -/
namespace OptimalQLS.Geometry

theorem denominator_pos {a t : ℝ} (ht : 0 < t) : 0 < a ^ 2 + t ^ 2 := by
  positivity

theorem eigenvalue_sq_lower {a t : ℝ} (ht : 0 ≤ t) (h : t ≤ |a|) :
    t ^ 2 ≤ a ^ 2 := by
  nlinarith [sq_abs a, sq_nonneg (|a| - t)]

theorem projection_coefficient_identity {a t : ℝ} (ht : 0 < t) :
    (t ^ 2 / (a ^ 2 + t ^ 2)) ^ 2 +
      (t * a / (a ^ 2 + t ^ 2)) ^ 2 = t ^ 2 / (a ^ 2 + t ^ 2) := by
  have hd := ne_of_gt (denominator_pos (a := a) ht)
  field_simp
  <;> ring

theorem projection_coefficient_bounds {a t : ℝ} (ht : 0 < t) (h : t ≤ |a|) :
    t ^ 2 / (2 * a ^ 2) ≤ t ^ 2 / (a ^ 2 + t ^ 2) ∧
    t ^ 2 / (a ^ 2 + t ^ 2) ≤ t ^ 2 / a ^ 2 ∧
    t ^ 2 / (a ^ 2 + t ^ 2) ≤ 1 / 2 := by
  have ha : 0 < a ^ 2 := lt_of_lt_of_le (sq_pos_of_pos ht) (eigenvalue_sq_lower ht.le h)
  have hd := denominator_pos (a := a) ht
  have ht2 := eigenvalue_sq_lower ht.le h
  refine ⟨?_, ?_, ?_⟩
  · apply div_le_div_of_nonneg_left (sq_nonneg t) hd
    linarith
  · apply div_le_div_of_nonneg_left (sq_nonneg t) ha
    nlinarith [sq_nonneg t]
  · rw [div_le_iff₀ hd]
    linarith

theorem pseudoinverse_coefficient_bound {a t : ℝ} (ht : 0 < t) (h : t ≤ |a|) :
    (a / (a ^ 2 + t ^ 2)) ^ 2 ≤ (a⁻¹) ^ 2 := by
  have ha : 0 < a ^ 2 := lt_of_lt_of_le (sq_pos_of_pos ht) (eigenvalue_sq_lower ht.le h)
  have hd := denominator_pos (a := a) ht
  rw [div_pow, inv_pow, ← one_div]
  apply (div_le_div_iff₀ (sq_pos_of_pos hd) ha).mpr
  nlinarith [sq_nonneg t, sq_nonneg (t ^ 2)]

theorem correction_coefficient_bounds {a t : ℝ} (ht : 0 < t) (h : t ≤ |a|) :
    1 ≤ 1 + t ^ 2 / a ^ 2 ∧ 1 + t ^ 2 / a ^ 2 ≤ 2 := by
  have ha : 0 < a ^ 2 := lt_of_lt_of_le (sq_pos_of_pos ht) (eigenvalue_sq_lower ht.le h)
  constructor
  · exact le_add_of_nonneg_right (div_nonneg (sq_nonneg t) ha.le)
  · have : t ^ 2 / a ^ 2 ≤ 1 := (div_le_one ha).mpr (eigenvalue_sq_lower ht.le h)
    linarith

theorem correction_coefficient_identity {a t : ℝ} (ha : a ≠ 0) (ht : 0 < t) :
    (1 + t ^ 2 / a ^ 2) * (a / (a ^ 2 + t ^ 2)) = a⁻¹ := by
  have hd := ne_of_gt (denominator_pos (a := a) ht)
  field_simp
  <;> ring

theorem auxiliary_eigenvalue_bounds {a t : ℝ} (ht : 0 < t)
    (hlo : t ≤ |a|) (hhi : |a| ≤ 1) :
    Real.sqrt 2 * t ≤ Real.sqrt (a ^ 2 + t ^ 2) ∧
      Real.sqrt (a ^ 2 + t ^ 2) ≤ Real.sqrt (1 + t ^ 2) := by
  have hl := eigenvalue_sq_lower ht.le hlo
  have hu : a ^ 2 ≤ 1 := by nlinarith [sq_abs a]
  have hd := denominator_pos (a := a) ht
  constructor
  · have hs := Real.sq_sqrt hd.le
    have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (a ^ 2 + t ^ 2), Real.sqrt_nonneg 2,
      mul_nonneg (Real.sqrt_nonneg 2) ht.le]
  · exact Real.sqrt_le_sqrt (by linarith)

end OptimalQLS.Geometry
