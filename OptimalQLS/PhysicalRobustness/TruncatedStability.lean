import OptimalQLS.PhysicalRobustness.SharpNormalization
import OptimalQLS.PhysicalRobustness.LowOverlap
import OptimalQLS.PhysicalRobustness.PerturbedGap

/-! Sharp support-aware stability for the actual high-spectral inverse.
This is an analytic theorem; no preparation or QSVT realization is assumed. -/
noncomputable section
namespace OptimalQLS.PhysicalRobustness
open Geometry PhysicalPadding Matrix
open scoped Matrix.Norms.L2Operator

section Abstract
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- Orthogonal low/high errors for the spectral truncation of a noisy matrix. -/
theorem truncated_solution_sq_error
    (J : E →ₗᵢ[ℂ] F) (A : E →L[ℂ] E) (hA : IsUnit A)
    (H B : F →L[ℂ] F) (hB : B.toLinearMap.IsSymmetric)
    (hHJ : ∀ x, H (J x) = J (A x))
    {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 ≤ δ)
    (hinv : ‖Ring.inverse A‖ ≤ κ) (hpert : ‖B-H‖ ≤ δ) (hsmall : κ*δ < 1)
    (hgap : ∀ i, |hB.eigenvalues rfl i| ≤ δ ∨ κ⁻¹-δ ≤ |hB.eigenvalues rfl i|)
    (b : E) :
    ‖J (Ring.inverse A b)-highInverse B hB δ (J b)‖^2 ≤
      2*(κ*δ/(1-κ*δ))^2*‖Ring.inverse A b‖^2 := by
  let Q := lowProjector B hB δ
  let T := highInverse B hB δ
  let y := J (Ring.inverse A b)
  let z := T (J b)
  let r := κ*δ/(1-κ*δ)
  have hr : 0 ≤ r := div_nonneg (mul_nonneg hκ.le hδ) (sub_pos.mpr hsmall).le
  have hg : 0 < κ⁻¹-δ := by
    rw [inv_eq_one_div]
    exact sub_pos.mpr ((lt_div_iff₀ hκ).mpr (by nlinarith))
  have hginv : (κ⁻¹-δ)⁻¹ = κ/(1-κ*δ) := by
    field_simp
  have hT : ‖T‖ ≤ κ/(1-κ*δ) := by
    rw [← hginv]
    exact highInverse_norm B hB hg hgap
  have hQy : ‖Q y‖ ≤ r*‖y‖ := by
    rw [show ‖y‖ = ‖Ring.inverse A b‖ from J.norm_map _]
    exact lowProjector_active_apply J A hA H B hB hHJ hκ.le hδ hinv hpert hsmall _
  have hTy : ‖T ((B-H) y)‖ ≤ r*‖y‖ := by
    calc
      _ ≤ ‖T‖*‖(B-H) y‖ := T.le_opNorm _
      _ ≤ (κ/(1-κ*δ))*(δ*‖y‖) := by
        apply mul_le_mul hT
          (((B-H).le_opNorm y).trans (mul_le_mul_of_nonneg_right hpert (norm_nonneg _)))
          (norm_nonneg _) (div_nonneg hκ.le (sub_pos.mpr hsmall).le)
      _ = r*‖y‖ := by dsimp [r]; ring
  have hdecomp : y-z = Q y+T ((B-H) y) := by
    have htby := congrArg (fun L : F →L[ℂ] F => L y) (highInverse_mul_self B hB hδ)
    change T (B y) = y-Q y at htby
    have hhy : H y = J b := by
      dsimp [y]
      rw [hHJ, Perturbation.apply_inverse A hA]
    rw [ContinuousLinearMap.sub_apply, map_sub, htby, hhy]
    dsimp [z]
    abel
  have horth : inner ℂ (Q y) (T ((B-H) y)) = 0 := by
    have hsym : Q.toLinearMap.IsSymmetric := lowProjector_symmetric B hB δ
    change inner ℂ (Q.toLinearMap y) _ = 0
    rw [hsym]
    have hzero := congrArg (fun L : F →L[ℂ] F => L ((B-H) y))
      (lowProjector_mul_highInverse B hB δ)
    change Q (T ((B-H) y)) = 0 at hzero
    change inner ℂ y (Q (T ((B-H) y))) = 0
    rw [hzero, inner_zero_right]
  have hs : ‖y-z‖^2 ≤ 2*r^2*‖y‖^2 := by
    rw [hdecomp, norm_add_sq (𝕜 := ℂ), horth, RCLike.zero_re]
    have h₁ := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr (norm_nonneg _))).mpr hQy
    have h₂ := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr (norm_nonneg _))).mpr hTy
    nlinarith
  simpa only [y, J.norm_map] using hs

/-- The high-spectral solution keeps a constant-factor solution scale. -/
theorem truncated_solution_norm_bounds
    (J : E →ₗᵢ[ℂ] F) (A : E →L[ℂ] E) (hA : IsUnit A)
    (H B : F →L[ℂ] F) (hB : B.toLinearMap.IsSymmetric)
    (hHJ : ∀ x, H (J x) = J (A x))
    {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 ≤ δ)
    (hinv : ‖Ring.inverse A‖ ≤ κ) (hpert : ‖B-H‖ ≤ δ) (hsmall : κ*δ ≤ 1/4)
    (hgap : ∀ i, |hB.eigenvalues rfl i| ≤ δ ∨ κ⁻¹-δ ≤ |hB.eigenvalues rfl i|)
    (b : E) :
    ‖Ring.inverse A b‖/2 ≤ ‖highInverse B hB δ (J b)‖ ∧
    ‖highInverse B hB δ (J b)‖ ≤ 3*‖Ring.inverse A b‖/2 := by
  let r := κ*δ/(1-κ*δ)
  have hd : 0 < 1-κ*δ := by linarith
  have hr0 : 0 ≤ r := div_nonneg (mul_nonneg hκ.le hδ) hd.le
  have hr : r ≤ 1/3 := (div_le_iff₀ hd).mpr (by nlinarith)
  have hc : 2*r^2 ≤ 1/4 := by nlinarith
  have hs := truncated_solution_sq_error J A hA H B hB hHJ hκ hδ hinv hpert
    (by linarith : κ*δ < 1) hgap b
  have he : ‖J (Ring.inverse A b)-highInverse B hB δ (J b)‖ ≤ ‖Ring.inverse A b‖/2 := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖Ring.inverse A b‖)
    change ‖J (Ring.inverse A b)-highInverse B hB δ (J b)‖^2 ≤ 2*r^2*‖Ring.inverse A b‖^2 at hs
    nlinarith
  have hn := abs_norm_sub_norm_le (J (Ring.inverse A b)) (highInverse B hB δ (J b))
  rw [J.norm_map] at hn
  have ha := abs_le.mp (hn.trans he)
  constructor <;> linarith

/-- The normalized truncated inverse obeys exactly the paper's `2κδ` error
constant on an original active input. -/
theorem truncated_solution_normalized_error
    (J : E →ₗᵢ[ℂ] F) (A : E →L[ℂ] E) (hA : IsUnit A)
    (H B : F →L[ℂ] F) (hB : B.toLinearMap.IsSymmetric)
    (hHJ : ∀ x, H (J x) = J (A x))
    {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 ≤ δ)
    (hinv : ‖Ring.inverse A‖ ≤ κ) (hpert : ‖B-H‖ ≤ δ) (hsmall : κ*δ ≤ 1/4)
    (hgap : ∀ i, |hB.eigenvalues rfl i| ≤ δ ∨ κ⁻¹-δ ≤ |hB.eigenvalues rfl i|)
    (b : E) (hb : b ≠ 0) :
    highInverse B hB δ (J b) ≠ 0 ∧
    ‖NormedSpace.normalize (highInverse B hB δ (J b))-
      J (NormedSpace.normalize (Ring.inverse A b))‖ ≤ 2*κ*δ := by
  letI : InnerProductSpace ℝ F := InnerProductSpace.rclikeToReal ℂ F
  have hsq := truncated_solution_sq_error J A hA H B hB hHJ hκ hδ hinv hpert
    (by linarith : κ*δ < 1) hgap b
  have hy : J (Ring.inverse A b) ≠ 0 := by
    intro hz
    apply Perturbation.inverse_apply_ne_zero A hA hb
    apply J.injective
    simpa only [map_zero] using hz
  have hs := normalize_sub_le_two_rho_of_sq_error (J (Ring.inverse A b))
    (highInverse B hB δ (J b)) hy (mul_nonneg hκ.le hδ) hsmall
    (by simpa only [J.norm_map] using hsq)
  refine ⟨hs.1,?_⟩
  rw [← isometry_normalize, norm_sub_rev]
  simpa only [mul_assoc] using hs.2
end Abstract

end OptimalQLS.PhysicalRobustness
