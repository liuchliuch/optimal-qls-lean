import OptimalQLS.Perturbation.Lemma71
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Analytic promise transfer for Theorem 7.2

These are concrete consequences of Lemma 7.1 used by the fixed approximate
block-encoding theorem. They do not assert the existence of a quantum
algorithm: the circuit and its exact-encoding guarantee are separate tasks.
-/

noncomputable section
namespace OptimalQLS.Perturbation

/-- Purely scalar form of the norm-estimate transfer. -/
theorem relaxed_estimate_transfer {s t ŝ ρ : ℝ}
    (ht : 0 ≤ t) (hρ : ρ ≤ 1 / 4)
    (hlow : (1 - ρ) * t ≤ s) (hhigh : s ≤ (1 + ρ) * t)
    (hestlow : s / 2 ≤ ŝ) (hesthigh : ŝ ≤ 2 * s) :
    3 * t / 8 ≤ ŝ ∧ ŝ ≤ 5 * t / 2 := by
  have hmul : ρ * t ≤ (1 / 4) * t := mul_le_mul_of_nonneg_right hρ ht
  constructor <;> nlinarith

section Operators
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The block-encoding approximation bound implies the relative
perturbation hypothesis with `ρ = κ δ / α`. -/
theorem relative_error_of_absolute (A B : E →L[𝕜] E) {α κ δ : ℝ}
    (hα : 0 < α) (hδ : 0 ≤ δ)
    (hκ : α * ‖Ring.inverse A‖ ≤ κ) (herror : ‖B - A‖ ≤ δ) :
    ‖Ring.inverse A‖ * ‖B - A‖ ≤ κ * δ / α := by
  have hinv : ‖Ring.inverse A‖ ≤ κ / α :=
    (le_div_iff₀ hα).mpr (by nlinarith [hκ])
  calc
    ‖Ring.inverse A‖ * ‖B - A‖ ≤ ‖Ring.inverse A‖ * δ :=
      mul_le_mul_of_nonneg_left herror (norm_nonneg _)
    _ ≤ (κ / α) * δ := mul_le_mul_of_nonneg_right hinv hδ
    _ = κ * δ / α := by ring

/-- All of the analytic promises passed to the exact solver in Theorem 7.2,
including the paper's relaxed estimate constants `3/8` and `5/2`. -/
theorem fixed_approximate_encoding_promises [NormedSpace ℝ E] [CompleteSpace E] (A B : E →L[𝕜] E)
    (hA : IsUnit A) (b : E) (hb : b ≠ 0) {α κ δ ŝ : ℝ}
    (hα : 0 < α) (hδ : 0 ≤ δ)
    (hκ : α * ‖Ring.inverse A‖ ≤ κ) (herror : ‖B - A‖ ≤ δ)
    (hsmall : κ * δ / α ≤ 1 / 4)
    (hestlow : α * ‖Ring.inverse A b‖ / 2 ≤ ŝ)
    (hesthigh : ŝ ≤ 2 * (α * ‖Ring.inverse A b‖)) :
    IsUnit B ∧
    α * ‖Ring.inverse B‖ ≤ 4 * κ / 3 ∧
    3 * (α * ‖Ring.inverse B b‖) / 8 ≤ ŝ ∧
    ŝ ≤ 5 * (α * ‖Ring.inverse B b‖) / 2 ∧
    ‖NormedSpace.normalize (Ring.inverse B b) -
      NormedSpace.normalize (Ring.inverse A b)‖ ≤ 2 * κ * δ / α := by
  let ρ := κ * δ / α
  have hκ0 : 0 ≤ κ := (mul_nonneg hα.le (norm_nonneg _)).trans hκ
  have hρ0 : 0 ≤ ρ := div_nonneg (mul_nonneg hκ0 hδ) hα.le
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith [hsmall]
  have hpert := relative_error_of_absolute A B hα hδ hκ herror
  have hfull := lemma71 A B hA b hb hρ0 hρ1 hpert
  have hB := hfull.1
  have hinv : α * ‖Ring.inverse B‖ ≤ 4 * κ / 3 := by
    have hi := (le_div_iff₀ (sub_pos.mpr hρ1)).mp hfull.2.1
    have himul := mul_le_mul_of_nonneg_left hi hα.le
    have hrmul := mul_le_mul_of_nonneg_right hsmall
      (mul_nonneg hα.le (norm_nonneg (Ring.inverse B)))
    dsimp [ρ] at himul
    nlinarith
  have hnorm := solution_norm_comparison A B hA hB hpert b
  have hlow := mul_le_mul_of_nonneg_left hnorm.1 hα.le
  have hhigh := mul_le_mul_of_nonneg_left hnorm.2 hα.le
  have hest := relaxed_estimate_transfer (mul_nonneg hα.le (norm_nonneg _)) hsmall
    (by nlinarith [hlow] : (1 - κ * δ / α) * (α * ‖Ring.inverse B b‖) ≤
      α * ‖Ring.inverse A b‖)
    (by nlinarith [hhigh] : α * ‖Ring.inverse A b‖ ≤
      (1 + κ * δ / α) * (α * ‖Ring.inverse B b‖)) hestlow hesthigh
  refine ⟨hB, hinv, hest.1, hest.2, ?_⟩
  calc
    _ ≤ 2 * ρ := hfull.2.2.2.2
    _ = 2 * κ * δ / α := by dsimp [ρ]; ring

/-- The additive accuracy guarantee of Theorem 7.2, conditional only on
an output satisfying the exact-solver accuracy bound for the actual encoded
operator `B`. No algorithmic guarantee is postulated inside this theorem. -/
theorem fixed_approximate_encoding_output_error [NormedSpace ℝ E] [CompleteSpace E]
    (A B : E →L[𝕜] E) (hA : IsUnit A) (b : E) (hb : b ≠ 0)
    {α κ δ ε : ℝ} (hα : 0 < α) (hδ : 0 ≤ δ)
    (hκ : α * ‖Ring.inverse A‖ ≤ κ) (herror : ‖B - A‖ ≤ δ)
    (hsmall : κ * δ / α ≤ 1 / 4)
    (x : E) (hx : ‖x - NormedSpace.normalize (Ring.inverse B b)‖ ≤ ε) :
    ‖x - NormedSpace.normalize (Ring.inverse A b)‖ ≤ ε + 2 * κ * δ / α := by
  have hκ0 : 0 ≤ κ := (mul_nonneg hα.le (norm_nonneg _)).trans hκ
  have hρ0 : 0 ≤ κ * δ / α := div_nonneg (mul_nonneg hκ0 hδ) hα.le
  have hρ1 : κ * δ / α < 1 := by linarith
  have hpert := relative_error_of_absolute A B hα hδ hκ herror
  calc
    _ ≤ ε + 2 * (κ * δ / α) := approximate_output_error A B hA b hb hρ0 hρ1 hpert x hx
    _ = ε + 2 * κ * δ / α := by ring

/-- The vector-query coefficient transfer appearing at the end of
Theorem 7.2's proof. -/
theorem vector_query_coefficient_transfer (A B : E →L[𝕜] E)
    (hA : IsUnit A) (hB : IsUnit B) (b : E) (hb : b ≠ 0)
    {α κ ρ : ℝ} (hα : 0 < α) (hκ : 0 ≤ κ) (hρ : ρ ≤ 1 / 4)
    (hpert : ‖Ring.inverse A‖ * ‖B - A‖ ≤ ρ) :
    (4 * κ / 3) / (α * ‖Ring.inverse B b‖) ≤
      (5 / 3) * (κ / (α * ‖Ring.inverse A b‖)) := by
  have hApos : 0 < α * ‖Ring.inverse A b‖ :=
    mul_pos hα (norm_pos_iff.mpr (inverse_apply_ne_zero A hA hb))
  have hBpos : 0 < α * ‖Ring.inverse B b‖ :=
    mul_pos hα (norm_pos_iff.mpr (inverse_apply_ne_zero B hB hb))
  have hnorm := (solution_norm_comparison A B hA hB hpert b).2
  have hrmul := mul_le_mul_of_nonneg_right hρ (norm_nonneg (Ring.inverse B b))
  have hcomp : 4 * (α * ‖Ring.inverse A b‖) ≤ 5 * (α * ‖Ring.inverse B b‖) := by
    have : 4 * ‖Ring.inverse A b‖ ≤ 5 * ‖Ring.inverse B b‖ := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hα.le]
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hBpos hApos).mpr
  nlinarith [mul_le_mul_of_nonneg_left hcomp hκ]
end Operators

/-- A concrete finite-dimensional complex Hilbert-space instantiation.
The norm is the Euclidean norm, and map norms are induced operator norms. -/
theorem lemma71_complex_euclidean (d : ℕ)
    (A B : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))
    (hA : IsUnit A) (b : EuclideanSpace ℂ (Fin d)) (hb : b ≠ 0)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hpert : ‖Ring.inverse A‖ * ‖B - A‖ ≤ ρ) :
    IsUnit B ∧
    ‖Ring.inverse B‖ ≤ ‖Ring.inverse A‖ / (1 - ρ) ∧
    ‖Ring.inverse A b‖ / (1 + ρ) ≤ ‖Ring.inverse B b‖ ∧
    ‖Ring.inverse B b‖ ≤ ‖Ring.inverse A b‖ / (1 - ρ) ∧
    ‖NormedSpace.normalize (Ring.inverse B b) -
      NormedSpace.normalize (Ring.inverse A b)‖ ≤ 2 * ρ :=
  lemma71 A B hA b hb hρ0 hρ1 hpert

end OptimalQLS.Perturbation
