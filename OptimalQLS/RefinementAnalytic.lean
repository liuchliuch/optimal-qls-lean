import OptimalQLS.Perturbation.Lemma71
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# Explicit error and repetition constants

Analytic components of Propositions 4.1, 5.6 and Theorem 5.7. These lemmas
do not assume or assert a QSVT implementation: the corresponding concrete
polynomial circuits remain a separate formalization obligation.
-/
noncomputable section
namespace OptimalQLS

theorem coarse_overlap_constant {β overlap err : ℝ}
    (hoverlap : 1 / 30 < overlap) (herr : err < 1 / 1000)
    (hβ : overlap - err ≤ β) : 1 / 32 < β := by linarith

section NormedSpace
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℝ E] [NormedSpace ℝ F]

/-- Matrix correction and filtering errors are combined before normalization. -/
theorem correction_filter_error (C D : E →L[ℝ] F) (y y₀ : E) (x : F)
    {η lam : ℝ} (hη : 0 ≤ η) (hC : ‖C‖ ≤ 3 / 4)
    (hCD : ‖C - D‖ ≤ η / 2) (hy : ‖y - y₀‖ ≤ η)
    (hy₀ : ‖y₀‖ ≤ 1) (hcorrect : D y₀ = lam • x) :
    ‖C y - lam • x‖ ≤ 2 * η := by
  have hid : C y - lam • x = C (y - y₀) + (C - D) y₀ := by
    simp only [map_sub, ContinuousLinearMap.sub_apply, hcorrect]
    abel
  rw [hid]
  calc
    ‖C (y - y₀) + (C - D) y₀‖ ≤ ‖C (y - y₀)‖ + ‖(C - D) y₀‖ := norm_add_le _ _
    _ ≤ (3 / 4) * η + (η / 2) * 1 := add_le_add
      ((C.le_opNorm _).trans (mul_le_mul hC hy (norm_nonneg _) (by norm_num)))
      (((C - D).le_opNorm _).trans
        (mul_le_mul hCD hy₀ (norm_nonneg _) (by linarith)))
    _ ≤ 2 * η := by linarith

/-- The exact numerical conclusion used for joint postselection in 5.6. -/
theorem refinement_state_and_probability (x z : E) (hx : ‖x‖ = 1)
    {ε lam : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hlam : 1 / 128 ≤ lam)
    (hz : ‖z - lam • x‖ ≤ 2 * (ε / 1024)) :
    z ≠ 0 ∧ ‖NormedSpace.normalize z - x‖ ≤ ε / 2 ∧ 1 / 65536 < ‖z‖ ^ 2 := by
  have hlampos : 0 < lam := by linarith
  have hlamnorm : ‖lam • x‖ = lam := by simp [norm_smul, hx, abs_of_pos hlampos]
  have hreverse := norm_sub_norm_le (lam • x) z
  rw [hlamnorm, norm_sub_rev] at hreverse
  have hznorm : 1 / 256 < ‖z‖ := by linarith
  have hzne : z ≠ 0 := norm_pos_iff.mp (by linarith : 0 < ‖z‖)
  have hxn : lam • x ≠ 0 := norm_ne_zero_iff.mp (by rw [hlamnorm]; exact hlampos.ne')
  have hn := Perturbation.normalize_sub_le z (lam • x) hzne hxn
  rw [NormedSpace.normalize_smul_of_pos hlampos,
    NormedSpace.normalize_eq_self_of_norm_eq_one hx, hlamnorm] at hn
  refine ⟨hzne, hn.trans ?_, ?_⟩
  · apply (div_le_iff₀ hlampos).mpr
    have hmul := mul_le_mul_of_nonneg_left hlam (le_of_lt hε0)
    nlinarith
  · nlinarith

end NormedSpace

end OptimalQLS
