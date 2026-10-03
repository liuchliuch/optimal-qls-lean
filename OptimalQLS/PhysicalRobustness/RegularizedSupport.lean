import OptimalQLS.PhysicalRobustness.RegularizedResolvent
import OptimalQLS.Preparation.Coarse

/-! Strong regularized solution bounds using actual active restriction. -/
noncomputable section
namespace OptimalQLS.PhysicalRobustness
open Geometry PhysicalPadding
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- A Hermitian imaginary correction to identity has a Pythagorean norm. -/
theorem identity_imaginary_norm_sq (A : E →L[ℂ] E)
    (hA : A.toLinearMap.IsSymmetric) (t : ℝ) (x : E) :
    ‖x+((t : ℂ)*Complex.I) • A x‖^2 = ‖x‖^2+t^2*‖A x‖^2 := by
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, norm_smul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one, mul_pow, sq_abs]
  have him : (inner ℂ x (A x)).im = 0 := hA.im_inner_self_apply x
  have hre : (((t : ℂ)*Complex.I)*inner ℂ x (A x)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, him]
  change ‖x‖^2+2*(((t : ℂ)*Complex.I)*inner ℂ x (A x)).re+t^2*‖A x‖^2 = _
  rw [hre]
  ring

/-- Active restriction yields a stronger lower bound than the two-sided
full-register resolvent comparison. Its constant is sufficient to retain
the existing preparation algorithm and every existing budget theorem. -/
theorem noisy_regularized_solution_lower
    (J : E →ₗᵢ[ℂ] F) (R : F →L[ℂ] E)
    (hRJ : ∀ x, R (J x)=x) (hRn : ∀ x, ‖R x‖ ≤ ‖x‖)
    (A : E →L[ℂ] E) (hA : A.toLinearMap.IsSymmetric) (hunit : IsUnit A)
    (H B : F →L[ℂ] F) (hB : B.toLinearMap.IsSymmetric)
    (hRH : ∀ x, R (H x)=A (R x))
    {κ t δ : ℝ} (hκ : 0 ≤ κ) (ht : 0 < t) (hδ : 0 ≤ δ)
    (hkt : κ*t ≤ 1/2) (hsmall : κ*δ ≤ 1/4)
    (hinv : ‖Ring.inverse A‖ ≤ κ) (hpert : ‖B-H‖ ≤ δ) (b : E) :
    2*‖Ring.inverse A b‖/3 ≤ ‖Ring.inverse (imaginaryShift B t) (J b)‖ := by
  let v := Ring.inverse (imaginaryShift B t) (J b)
  have hv : imaginaryShift B t v=J b :=
    Perturbation.apply_inverse _ (imaginaryShift_isUnit B hB ht) (J b)
  have hbeq : b=A (R v)+((t : ℂ)*Complex.I) • R v+R ((B-H) v) := by
    have h := congrArg R hv
    change R (B v+((t : ℂ)*Complex.I) • v)=R (J b) at h
    rw [map_add, map_smul, hRJ] at h
    rw [ContinuousLinearMap.sub_apply, map_sub, hRH]
    rw [← h]
    abel
  have heq : Ring.inverse A b =
      (R v+((t : ℂ)*Complex.I) • Ring.inverse A (R v))+Ring.inverse A (R ((B-H) v)) := by
    conv_lhs => rw [hbeq]
    rw [map_add, map_add, map_smul]
    have hi := congrArg (fun T : E →L[ℂ] E => T (R v)) (Ring.inverse_mul_cancel A hunit)
    change Ring.inverse A (A (R v))=R v at hi
    rw [hi]
  have hi (x : E) : ‖Ring.inverse A x‖ ≤ κ*‖x‖ :=
    ((Ring.inverse A).le_opNorm x).trans (mul_le_mul_of_nonneg_right hinv (norm_nonneg _))
  have htI : t*‖Ring.inverse A (R v)‖ ≤ ‖v‖/2 := by
    calc
      _ ≤ t*(κ*‖R v‖) := mul_le_mul_of_nonneg_left (hi _) ht.le
      _ ≤ (1/2)*‖R v‖ := by nlinarith [mul_le_mul_of_nonneg_right hkt (norm_nonneg (R v))]
      _ ≤ ‖v‖/2 := by linarith [hRn v]
  have hbase : ‖R v+((t : ℂ)*Complex.I) • Ring.inverse A (R v)‖ ≤ (5/4)*‖v‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [identity_imaginary_norm_sq _ (inverse_symmetric A hA hunit)]
    have hr2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hRn v)
    have ht2 := (sq_le_sq₀ (mul_nonneg ht.le (norm_nonneg _)) (by positivity)).mpr htI
    nlinarith [sq_nonneg ‖v‖]
  have herr : ‖Ring.inverse A (R ((B-H) v))‖ ≤ ‖v‖/4 := by
    calc
      _ ≤ κ*‖R ((B-H) v)‖ := hi _
      _ ≤ κ*‖(B-H) v‖ := mul_le_mul_of_nonneg_left (hRn _) hκ
      _ ≤ κ*(δ*‖v‖) := mul_le_mul_of_nonneg_left
        (((B-H).le_opNorm _).trans (mul_le_mul_of_nonneg_right hpert (norm_nonneg _))) hκ
      _ ≤ ‖v‖/4 := by nlinarith [mul_le_mul_of_nonneg_right hsmall (norm_nonneg v)]
  have hn : ‖Ring.inverse A b‖ ≤ (3/2)*‖v‖ := by
    rw [heq]
    exact (norm_add_le _ _).trans (by linarith)
  change 2*‖Ring.inverse A b‖/3 ≤ ‖v‖
  linarith

/-- Upper bound from the ordinary resolvent identity; only the original A is
required to be invertible. -/
theorem noisy_regularized_solution_upper
    (J : E →ₗᵢ[ℂ] F) (A : E →L[ℂ] E)
    (hA : A.toLinearMap.IsSymmetric) (hunit : IsUnit A)
    (H B : F →L[ℂ] F) (hB : B.toLinearMap.IsSymmetric)
    (hHJ : ∀ x, H (J x)=J (A x))
    {κ t δ : ℝ} (hκ : 0 ≤ κ) (ht : 0 < t) (hδ : 0 ≤ δ)
    (hdt : δ/t ≤ 1/2) (hinv : ‖Ring.inverse A‖ ≤ κ)
    (hpert : ‖B-H‖ ≤ δ) (b : E) :
    ‖Ring.inverse (imaginaryShift B t) (J b)‖ ≤ 3*‖Ring.inverse A b‖/2 := by
  have he := noisy_regularized_solution_error J A hA H B hB hHJ ht hδ hpert b
  have hc := (regularized_solution_comparison A hA hunit ht hκ hinv b).1
  have hnorm := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hc
  have hn := norm_sub_norm_le (Ring.inverse (imaginaryShift B t) (J b))
    (J (Ring.inverse (imaginaryShift A t) b))
  rw [J.norm_map] at hn
  have hm := mul_le_mul_of_nonneg_right hdt
    (norm_nonneg (Ring.inverse (imaginaryShift A t) b))
  linarith

/-- A unit source and a contraction B keep the regularized norm above 1/√2. -/
theorem regularized_solution_unit_lower (B : F →L[ℂ] F)
    (hB : B.toLinearMap.IsSymmetric) (hBn : ‖B‖ ≤ 1)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (b : F) (hb : ‖b‖=1) :
    1 ≤ 2*‖Ring.inverse (imaginaryShift B t) b‖^2 := by
  let v := Ring.inverse (imaginaryShift B t) b
  have he := imaginaryShift_norm_sq B hB t v
  rw [Perturbation.apply_inverse _ (imaginaryShift_isUnit B hB ht), hb] at he
  have hn : ‖B v‖ ≤ ‖v‖ :=
    (B.le_opNorm v).trans ((mul_le_mul_of_nonneg_right hBn (norm_nonneg _)).trans_eq (one_mul _))
  have hn2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn
  have ht2 : t^2 ≤ 1 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right ht2 (sq_nonneg ‖v‖)
  change 1 ≤ 2*‖v‖^2
  nlinarith

/-- Actual computational restriction is a contraction. -/
theorem restriction_norm_le {D P : Type*} [Fintype D] [DecidableEq D]
    [Fintype P] [DecidableEq P] (f : D ↪ P) (v : EuclideanSpace ℂ P) :
    ‖restriction f v‖ ≤ ‖v‖ := Preparation.coordinate_slice_norm_le f v

end OptimalQLS.PhysicalRobustness
