import OptimalQLS.Perturbation.Lemma71
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Sharp normalization for support-aware perturbation

The usual factor-two normalization inequality loses too much after splitting
an error into orthogonal high- and low-spectral pieces.  The following lemma
uses the angle between the vectors and proves the needed `2ρ` constant.
-/
noncomputable section
namespace OptimalQLS.PhysicalRobustness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A cone estimate: a vector in a relative ball of squared radius `1-t²`
has normalized inner product at least `t` with its center. -/
theorem normalized_inner_ge_of_sq_error (y z : E) (hy : y ≠ 0) (hz : z ≠ 0)
    {t : ℝ} (ht : 0 ≤ t)
    (herr : ‖y-z‖^2 ≤ (1-t^2)*‖y‖^2) :
    t ≤ inner ℝ (NormedSpace.normalize y) (NormedSpace.normalize z) := by
  have hY : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hZ : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have he := norm_sub_sq_real y z
  have hc : t * ‖y‖ * ‖z‖ ≤ inner ℝ y z := by
    nlinarith [sq_nonneg (‖z‖-t*‖y‖)]
  simp only [NormedSpace.normalize, real_inner_smul_left, real_inner_smul_right]
  have hp : 0 < ‖y‖*‖z‖ := mul_pos hY hZ
  calc
    t ≤ inner ℝ y z / (‖y‖*‖z‖) := (le_div_iff₀ hp).mpr (by nlinarith [hc])
    _ = ‖z‖⁻¹ * (‖y‖⁻¹ * inner ℝ y z) := by field_simp

/-- The preceding cone estimate expressed as a squared state distance. -/
theorem normalize_sub_sq_le_of_sq_error (y z : E) (hy : y ≠ 0) (hz : z ≠ 0)
    {t : ℝ} (ht : 0 ≤ t)
    (herr : ‖y-z‖^2 ≤ (1-t^2)*‖y‖^2) :
    ‖NormedSpace.normalize y-NormedSpace.normalize z‖^2 ≤ 2-2*t := by
  have hi := normalized_inner_ge_of_sq_error y z hy hz ht herr
  rw [norm_sub_sq_real, NormedSpace.norm_normalize hy, NormedSpace.norm_normalize hz]
  nlinarith

/-- Scalar slack available at the paper's `ρ ≤ 1/4` threshold. -/
theorem orthogonal_error_coefficient {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1/4) :
    2 * (ρ / (1-ρ))^2 ≤ 1-(1-2*ρ^2)^2 := by
  have hd : 0 < 1-ρ := by linarith
  have hsq : ρ^2 ≤ 1/16 := by nlinarith
  have hden : 9/16 ≤ (1-ρ)^2 := by nlinarith
  have hc : 2 ≤ 4*(1-ρ^2)*(1-ρ)^2 := by
    have hm := mul_le_mul (show (15/16 : ℝ) ≤ 1-ρ^2 by linarith) hden
      (by norm_num : (0 : ℝ) ≤ 9/16) (by nlinarith : 0 ≤ 1-ρ^2)
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hc (sq_nonneg ρ)
  rw [div_pow, ← mul_div_assoc]
  apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
  nlinarith

/-- Orthogonal perturbation errors of size `ρ/(1-ρ)` each still imply the
paper's state error `2ρ`; no inverse of a padded physical matrix is used. -/
theorem normalize_sub_le_two_rho_of_sq_error (y z : E) (hy : y ≠ 0)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1/4)
    (herr : ‖y-z‖^2 ≤ 2*(ρ/(1-ρ))^2*‖y‖^2) :
    z ≠ 0 ∧ ‖NormedSpace.normalize y-NormedSpace.normalize z‖ ≤ 2*ρ := by
  have hcoef := orthogonal_error_coefficient hρ0 hρ
  have ht : 0 < 1-2*ρ^2 := by nlinarith [sq_nonneg ρ]
  have herr' : ‖y-z‖^2 ≤ (1-(1-2*ρ^2)^2)*‖y‖^2 :=
    herr.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖y‖))
  have hz : z ≠ 0 := by
    intro hz
    rw [hz, sub_zero] at herr'
    have hY : 0 < ‖y‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hy)
    have hp := mul_pos (sq_pos_of_pos ht) hY
    nlinarith
  refine ⟨hz,?_⟩
  have hs := normalize_sub_sq_le_of_sq_error y z hy hz ht.le herr'
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2*ρ)).mp (by nlinarith)

end OptimalQLS.PhysicalRobustness
