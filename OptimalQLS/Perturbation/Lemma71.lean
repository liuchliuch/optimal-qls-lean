import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Lemma 7.1: inverse and solution perturbation

This module proves the analytic lemma in Section 7 of
*Simultaneously Query-Optimal Quantum Linear-System Algorithm*
(arXiv:2609.33686v1). Operators are genuine bounded linear maps on Banach
spaces, and invertibility is the algebraic `IsUnit` predicate. The proof of
invertibility uses mathlib's Neumann-series theorem.
-/

noncomputable section
namespace OptimalQLS.Perturbation

section Operators
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A perturbation satisfying the paper's relative operator-norm hypothesis
is invertible. The key unit `1 + A⁻¹(B-A)` is built by a Neumann series. -/
theorem isUnit_of_relative_perturbation [CompleteSpace E] (A B : E →L[𝕜] E)
    (hA : IsUnit A) {ρ : ℝ} (hρ : ρ < 1)
    (hpert : ‖Ring.inverse A‖ * ‖B - A‖ ≤ ρ) : IsUnit B := by
  let D := Ring.inverse A * (B - A)
  have hD : ‖D‖ < 1 := lt_of_le_of_lt (norm_mul_le _ _ |>.trans hpert) hρ
  have hC : IsUnit (1 + D) := by
    simpa only [sub_neg_eq_add] using
      (isUnit_one_sub_of_norm_lt_one (by simpa only [norm_neg] using hD) :
        IsUnit (1 - -D))
  have hfactor : A * (1 + D) = B := by
    dsimp [D]
    rw [mul_add, mul_one, ← mul_assoc, Ring.mul_inverse_cancel A hA, one_mul]
    abel
  exact hfactor ▸ hA.mul hC

/-- Applying an invertible operator to its inverse returns the input. -/
theorem apply_inverse (A : E →L[𝕜] E) (hA : IsUnit A) (b : E) :
    A (Ring.inverse A b) = b := by
  have h := congrArg (fun T : E →L[𝕜] E => T b) (Ring.mul_inverse_cancel A hA)
  simpa using h

/-- The inverse of an invertible bounded operator maps nonzero vectors to nonzero vectors. -/
theorem inverse_apply_ne_zero (A : E →L[𝕜] E) (hA : IsUnit A)
    {b : E} (hb : b ≠ 0) : Ring.inverse A b ≠ 0 := by
  intro hz
  have := apply_inverse A hA b
  rw [hz, map_zero] at this
  exact hb this.symm

/-- The two exact solutions obey the resolvent identity pointwise. -/
theorem solution_difference_eq (A B : E →L[𝕜] E)
    (hA : IsUnit A) (hB : IsUnit B) (b : E) :
    Ring.inverse A b - Ring.inverse B b =
      (Ring.inverse A * (B - A)) (Ring.inverse B b) := by
  have hleft : Ring.inverse A (A (Ring.inverse B b)) = Ring.inverse B b := by
    have h := congrArg (fun T : E →L[𝕜] E => T (Ring.inverse B b))
      (Ring.inverse_mul_cancel A hA)
    simpa using h
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply, map_sub]
  rw [apply_inverse B hB, hleft]

/-- The relative solution difference has denominator `‖B⁻¹b‖`, which is
what makes the final normalized bound `2ρ` rather than `2ρ/(1-ρ)`. -/
theorem solution_difference_le (A B : E →L[𝕜] E)
    (hA : IsUnit A) (hB : IsUnit B) {ρ : ℝ}
    (hpert : ‖Ring.inverse A‖ * ‖B - A‖ ≤ ρ) (b : E) :
    ‖Ring.inverse A b - Ring.inverse B b‖ ≤ ρ * ‖Ring.inverse B b‖ := by
  rw [solution_difference_eq A B hA hB]
  exact ((Ring.inverse A * (B - A)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans hpert) (norm_nonneg _))

/-- Multiplicative (division-free) form of the two solution norm bounds. -/
theorem solution_norm_comparison (A B : E →L[𝕜] E)
    (hA : IsUnit A) (hB : IsUnit B) {ρ : ℝ}
    (hpert : ‖Ring.inverse A‖ * ‖B - A‖ ≤ ρ) (b : E) :
    (1 - ρ) * ‖Ring.inverse B b‖ ≤ ‖Ring.inverse A b‖ ∧
    ‖Ring.inverse A b‖ ≤ (1 + ρ) * ‖Ring.inverse B b‖ := by
  have hdiff := solution_difference_le A B hA hB hpert b
  have hnorm := abs_norm_sub_norm_le (Ring.inverse A b) (Ring.inverse B b)
  have hlower := (abs_le.mp (hnorm.trans hdiff)).1
  have hupper := (abs_le.mp (hnorm.trans hdiff)).2
  constructor <;> nlinarith

/-- Equation (7.1): the inverse norm bound, derived pointwise from the
solution comparison and the operator-norm characterization. -/
theorem inverse_norm_le (A B : E →L[𝕜] E)
    (hA : IsUnit A) (hB : IsUnit B) {ρ : ℝ} (hρ : ρ < 1)
    (hpert : ‖Ring.inverse A‖ * ‖B - A‖ ≤ ρ) :
    ‖Ring.inverse B‖ ≤ ‖Ring.inverse A‖ / (1 - ρ) := by
  have hden : 0 < 1 - ρ := sub_pos.mpr hρ
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (norm_nonneg _) hden.le)
  intro b
  have hlow := (solution_norm_comparison A B hA hB hpert b).1
  have hnorm := (Ring.inverse A).le_opNorm b
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hden).mpr
  nlinarith

/-- The inverse difference satisfies the usual resolvent bound as well.
This is a supplementary consequence, not an extra assumption of Lemma 7.1. -/
theorem inverse_difference_le (A B : E →L[𝕜] E)
    (hA : IsUnit A) (hB : IsUnit B) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hpert : ‖Ring.inverse A‖ * ‖B - A‖ ≤ ρ) :
    ‖Ring.inverse B - Ring.inverse A‖ ≤ ρ * ‖Ring.inverse A‖ / (1 - ρ) := by
  have hidentity : Ring.inverse A - Ring.inverse B =
      (Ring.inverse A * (B - A)) * Ring.inverse B := by
    ext b
    simpa using solution_difference_eq A B hA hB b
  rw [norm_sub_rev, hidentity]
  calc
    ‖Ring.inverse A * (B - A) * Ring.inverse B‖ ≤
        (‖Ring.inverse A‖ * ‖B - A‖) * ‖Ring.inverse B‖ :=
      (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ ρ * ‖Ring.inverse B‖ := mul_le_mul_of_nonneg_right hpert (norm_nonneg _)
    _ ≤ ρ * (‖Ring.inverse A‖ / (1 - ρ)) :=
      mul_le_mul_of_nonneg_left (inverse_norm_le A B hA hB hρ1 hpert) hρ0
    _ = ρ * ‖Ring.inverse A‖ / (1 - ρ) := by ring

/-- Equation (7.2): upper and lower solution-norm bounds. -/
theorem solution_norm_bounds (A B : E →L[𝕜] E)
    (hA : IsUnit A) (hB : IsUnit B) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hpert : ‖Ring.inverse A‖ * ‖B - A‖ ≤ ρ) (b : E) :
    ‖Ring.inverse A b‖ / (1 + ρ) ≤ ‖Ring.inverse B b‖ ∧
    ‖Ring.inverse B b‖ ≤ ‖Ring.inverse A b‖ / (1 - ρ) := by
  have hc := solution_norm_comparison A B hA hB hpert b
  constructor
  · apply (div_le_iff₀ (show 0 < 1 + ρ by linarith)).mpr
    nlinarith [hc.2]
  · apply (le_div_iff₀ (sub_pos.mpr hρ1)).mpr
    nlinarith [hc.1]
end Operators

section Normalization
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Normalization is locally Lipschitz with the asymmetric denominator
needed for the sharp `2ρ` perturbation bound. -/
theorem normalize_sub_le (y z : E) (hy : y ≠ 0) (hz : z ≠ 0) :
    ‖NormedSpace.normalize y - NormedSpace.normalize z‖ ≤ 2 * ‖y - z‖ / ‖z‖ := by
  have hyn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hzn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hid : ‖y‖⁻¹ - ‖z‖⁻¹ = (‖z‖ - ‖y‖) / (‖y‖ * ‖z‖) := by
    field_simp
  have hfirst : ‖NormedSpace.normalize y - ‖z‖⁻¹ • y‖ =
      |‖z‖ - ‖y‖| / ‖z‖ := by
    rw [NormedSpace.normalize, ← sub_smul, norm_smul, Real.norm_eq_abs, hid,
      abs_div, abs_mul, abs_of_nonneg (norm_nonneg y), abs_of_nonneg (norm_nonneg z)]
    field_simp
  have hsecond : ‖‖z‖⁻¹ • y - NormedSpace.normalize z‖ = ‖y - z‖ / ‖z‖ := by
    rw [NormedSpace.normalize, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hzpos), div_eq_mul_inv, mul_comm]
  calc
    ‖NormedSpace.normalize y - NormedSpace.normalize z‖ ≤
        ‖NormedSpace.normalize y - ‖z‖⁻¹ • y‖ +
          ‖‖z‖⁻¹ • y - NormedSpace.normalize z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = (|‖z‖ - ‖y‖| + ‖y - z‖) / ‖z‖ := by rw [hfirst, hsecond, add_div]
    _ ≤ 2 * ‖y - z‖ / ‖z‖ := by
      apply div_le_div_of_nonneg_right _ hzpos.le
      have h := abs_norm_sub_norm_le z y
      rw [norm_sub_rev z y] at h
      linarith

/-- If the error is bounded relative to the second vector, normalized
vectors differ by at most twice the same relative error. -/
theorem normalize_sub_le_of_relative (y z : E) (hy : y ≠ 0) (hz : z ≠ 0)
    {ρ : ℝ} (h : ‖y - z‖ ≤ ρ * ‖z‖) :
    ‖NormedSpace.normalize y - NormedSpace.normalize z‖ ≤ 2 * ρ := by
  refine (normalize_sub_le y z hy hz).trans ?_
  apply (div_le_iff₀ (norm_pos_iff.mpr hz)).mpr
  linarith
end Normalization

section FullLemma
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Lemma 7.1**, in full. On a complex Euclidean space these are exactly
all three displayed estimates in the paper. The proof works more generally
for Banach spaces; it does not assume Hermiticity or normality. -/
theorem lemma71 (A B : E →L[𝕜] E) (hA : IsUnit A)
    (b : E) (hb : b ≠ 0) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hpert : ‖Ring.inverse A‖ * ‖B - A‖ ≤ ρ) :
    IsUnit B ∧
    ‖Ring.inverse B‖ ≤ ‖Ring.inverse A‖ / (1 - ρ) ∧
    ‖Ring.inverse A b‖ / (1 + ρ) ≤ ‖Ring.inverse B b‖ ∧
    ‖Ring.inverse B b‖ ≤ ‖Ring.inverse A b‖ / (1 - ρ) ∧
    ‖NormedSpace.normalize (Ring.inverse B b) -
      NormedSpace.normalize (Ring.inverse A b)‖ ≤ 2 * ρ := by
  have hB := isUnit_of_relative_perturbation A B hA hρ1 hpert
  have hnorm := solution_norm_bounds A B hA hB hρ0 hρ1 hpert b
  refine ⟨hB, inverse_norm_le A B hA hB hρ1 hpert, hnorm.1, hnorm.2, ?_⟩
  rw [norm_sub_rev]
  exact normalize_sub_le_of_relative _ _ (inverse_apply_ne_zero A hA hb)
    (inverse_apply_ne_zero B hB hb) (solution_difference_le A B hA hB hpert b)

/-- The final triangle-inequality step used in Theorem 7.2. -/
theorem approximate_output_error (A B : E →L[𝕜] E) (hA : IsUnit A)
    (b : E) (hb : b ≠ 0) {ρ ε : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hpert : ‖Ring.inverse A‖ * ‖B - A‖ ≤ ρ)
    (x : E) (hx : ‖x - NormedSpace.normalize (Ring.inverse B b)‖ ≤ ε) :
    ‖x - NormedSpace.normalize (Ring.inverse A b)‖ ≤ ε + 2 * ρ := by
  have hstate := (lemma71 A B hA b hb hρ0 hρ1 hpert).2.2.2.2
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hx hstate)
end FullLemma

end OptimalQLS.Perturbation
