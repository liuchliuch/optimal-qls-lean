import OptimalQLS.PhysicalRobustness.PhysicalEndpoint
import OptimalQLS.Geometry.GeneralCorrection
import Mathlib.Analysis.Normed.Operator.Banach

/-! Imaginary shifted resolvents remain well conditioned even when the full
physical matrix is singular.  These estimates prepare the noisy graph analysis. -/
noncomputable section
namespace OptimalQLS.PhysicalRobustness
open Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Shift by a nonzero imaginary scalar, without changing the data support. -/
def imaginaryShift (H : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E :=
  H+((t : ℂ)*Complex.I) • (1 : E →L[ℂ] E)

/-- Orthogonality of the real and imaginary Hermitian contributions. -/
theorem imaginaryShift_norm_sq (H : E →L[ℂ] E) (hH : H.toLinearMap.IsSymmetric)
    (t : ℝ) (x : E) : ‖imaginaryShift H t x‖^2 = ‖H x‖^2+t^2*‖x‖^2 := by
  change ‖H x+((t : ℂ)*Complex.I) • x‖^2 = _
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, norm_smul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one, mul_pow, sq_abs]
  have him : (inner ℂ (H x) x).im = 0 := hH.im_inner_apply_self x
  have hre : (((t : ℂ)*Complex.I)*inner ℂ (H x) x).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, him]
  change ‖H x‖^2+2*(((t : ℂ)*Complex.I)*inner ℂ (H x) x).re+t^2*‖x‖^2 = _
  rw [hre]
  ring

theorem imaginaryShift_norm_lower (H : E →L[ℂ] E) (hH : H.toLinearMap.IsSymmetric)
    {t : ℝ} (ht : 0 ≤ t) (x : E) : t*‖x‖ ≤ ‖imaginaryShift H t x‖ := by
  apply (sq_le_sq₀ (mul_nonneg ht (norm_nonneg _)) (norm_nonneg _)).mp
  rw [mul_pow, imaginaryShift_norm_sq H hH]
  nlinarith [sq_nonneg ‖H x‖]

/-- Every finite Hermitian operator has an invertible nonzero imaginary shift,
including the singular full physical compression. -/
theorem imaginaryShift_isUnit (H : E →L[ℂ] E) (hH : H.toLinearMap.IsSymmetric)
    {t : ℝ} (ht : 0 < t) : IsUnit (imaginaryShift H t) := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot,
    LinearMap.ker_eq_bot']
  intro x hx
  have hn := imaginaryShift_norm_lower H hH ht.le x
  change imaginaryShift H t x = 0 at hx
  rw [hx, norm_zero] at hn
  have hzero : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
  exact norm_eq_zero.mp hzero

/-- Uniform imaginary-resolvent norm bound `1/t`. -/
theorem imaginaryShift_inverse_norm (H : E →L[ℂ] E) (hH : H.toLinearMap.IsSymmetric)
    {t : ℝ} (ht : 0 < t) : ‖Ring.inverse (imaginaryShift H t)‖ ≤ t⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr ht.le)
  intro x
  have hn := imaginaryShift_norm_lower H hH ht.le (Ring.inverse (imaginaryShift H t) x)
  rw [Perturbation.apply_inverse _ (imaginaryShift_isUnit H hH ht)] at hn
  calc
    _ ≤ ‖x‖/t := (le_div_iff₀ ht).mpr (by nlinarith)
    _ = t⁻¹*‖x‖ := by ring

/-- On the original invertible matrix the regularized solution has squared
norm between `s²/(1+t²κ²)` and `s²`. -/
theorem regularized_solution_comparison (A : E →L[ℂ] E)
    (hA : A.toLinearMap.IsSymmetric) (hunit : IsUnit A)
    {t κ : ℝ} (ht : 0 < t) (hκ : 0 ≤ κ) (hinv : ‖Ring.inverse A‖ ≤ κ) (b : E) :
    ‖Ring.inverse (imaginaryShift A t) b‖^2 ≤ ‖Ring.inverse A b‖^2 ∧
    ‖Ring.inverse A b‖^2 ≤ (1+t^2*κ^2)*‖Ring.inverse (imaginaryShift A t) b‖^2 := by
  let v := Ring.inverse (imaginaryShift A t) b
  have hAv : imaginaryShift A t v = b :=
    Perturbation.apply_inverse _ (imaginaryShift_isUnit A hA ht) b
  have heq : Ring.inverse A b = v+((t : ℂ)*Complex.I) • Ring.inverse A v := by
    rw [← hAv]
    change Ring.inverse A (A v+((t : ℂ)*Complex.I) • v) = _
    rw [map_add, map_smul]
    have hi := congrArg (fun T : E →L[ℂ] E => T v) (Ring.inverse_mul_cancel A hunit)
    change Ring.inverse A (A v) = v at hi
    rw [hi]
  have hnorm : ‖Ring.inverse A b‖^2 = ‖v‖^2+t^2*‖Ring.inverse A v‖^2 := by
    rw [heq, norm_add_sq (𝕜 := ℂ), inner_smul_right, norm_smul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one, mul_pow, sq_abs]
    have him : (inner ℂ v (Ring.inverse A v)).im = 0 :=
      (inverse_symmetric A hA hunit).im_inner_self_apply v
    have hre : (((t : ℂ)*Complex.I)*inner ℂ v (Ring.inverse A v)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im, him]
    change ‖v‖^2+2*(((t : ℂ)*Complex.I)*inner ℂ v (Ring.inverse A v)).re+
      t^2*‖Ring.inverse A v‖^2 = _
    rw [hre]
    ring
  have hv : ‖Ring.inverse A v‖ ≤ κ*‖v‖ :=
    ((Ring.inverse A).le_opNorm v).trans (mul_le_mul_of_nonneg_right hinv (norm_nonneg _))
  have hvsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hκ (norm_nonneg _))).mpr hv
  constructor
  · change ‖v‖^2 ≤ _
    rw [hnorm]
    nlinarith [mul_nonneg (sq_nonneg t) (sq_nonneg ‖Ring.inverse A v‖)]
  · change _ ≤ (1+t^2*κ^2)*‖v‖^2
    rw [hnorm]
    have hm := mul_le_mul_of_nonneg_left hvsq (sq_nonneg t)
    nlinarith

section Transport
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- Perturbation of the imaginary resolvent on the original support. The
relative denominator is the logical regularized solution, not a padded inverse. -/
theorem noisy_regularized_solution_error (J : E →ₗᵢ[ℂ] F)
    (A : E →L[ℂ] E) (hA : A.toLinearMap.IsSymmetric)
    (H B : F →L[ℂ] F) (hB : B.toLinearMap.IsSymmetric)
    (hHJ : ∀ x, H (J x)=J (A x))
    {t δ : ℝ} (ht : 0 < t) (hδ : 0 ≤ δ) (hpert : ‖B-H‖ ≤ δ) (b : E) :
    ‖Ring.inverse (imaginaryShift B t) (J b)-J (Ring.inverse (imaginaryShift A t) b)‖
      ≤ (δ/t)*‖Ring.inverse (imaginaryShift A t) b‖ := by
  let v := Ring.inverse (imaginaryShift A t) b
  let R := Ring.inverse (imaginaryShift B t)
  have hAv : imaginaryShift A t v = b :=
    Perturbation.apply_inverse _ (imaginaryShift_isUnit A hA ht) b
  have hshift : imaginaryShift B t (J v)=J b+(B-H) (J v) := by
    rw [← hAv]
    change B (J v)+((t : ℂ)*Complex.I) • J v =
      J (A v+((t : ℂ)*Complex.I) • v)+(B (J v)-H (J v))
    rw [map_add, map_smul, hHJ]
    abel
  have heq : R (J b)-J v = -R ((B-H) (J v)) := by
    have hi := congrArg (fun T : F →L[ℂ] F => T (J v))
      (Ring.inverse_mul_cancel (imaginaryShift B t) (imaginaryShift_isUnit B hB ht))
    change R (imaginaryShift B t (J v))=J v at hi
    rw [hshift, map_add] at hi
    calc
      R (J b)-J v = R (J b)-(R (J b)+R ((B-H) (J v))) :=
        congrArg (fun w : F => R (J b)-w) hi.symm
      _ = -R ((B-H) (J v)) := by abel
  change ‖R (J b)-J v‖ ≤ _
  rw [heq, norm_neg]
  calc
    _ ≤ ‖R‖*‖(B-H) (J v)‖ := R.le_opNorm _
    _ ≤ t⁻¹*(δ*‖J v‖) := mul_le_mul (imaginaryShift_inverse_norm B hB ht)
      (((B-H).le_opNorm _).trans (mul_le_mul_of_nonneg_right hpert (norm_nonneg _)))
      (norm_nonneg _) (inv_nonneg.mpr ht.le)
    _ = (δ/t)*‖v‖ := by rw [J.norm_map]; ring
end Transport

end OptimalQLS.PhysicalRobustness
