import OptimalQLS.PhysicalRobustness.RegularizedSupport

/-! Exact graph geometry in terms of the imaginary resolvent, valid on every
Hermitian full-register matrix including singular noisy inputs. -/
noncomputable section
namespace OptimalQLS.PhysicalRobustness
open Geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Spectral coordinates of the actual shifted inverse. -/
theorem imaginaryShift_inverse_coordinates (A : E →L[ℂ] E)
    (hA : A.toLinearMap.IsSymmetric) {t : ℝ} (ht : 0 < t) (b : E)
    (i : Fin (Module.finrank ℂ E)) :
    (hA.eigenvectorBasis rfl).repr (Ring.inverse (imaginaryShift A t) b) i =
      (hA.eigenvectorBasis rfl).repr b i /
        ((hA.eigenvalues rfl i : ℂ)+(t : ℂ)*Complex.I) := by
  let U := (hA.eigenvectorBasis rfl).repr
  let v := Ring.inverse (imaginaryShift A t) b
  have hn : (hA.eigenvalues rfl i : ℂ)+(t : ℂ)*Complex.I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at him
    exact ht.ne' him
  have hv := congrArg (fun x : E => U x i)
    (Perturbation.apply_inverse (imaginaryShift A t) (imaginaryShift_isUnit A hA ht) b)
  change U (A v+((t : ℂ)*Complex.I) • v) i=U b i at hv
  rw [map_add, map_smul] at hv
  have hd : U (A v) i=(hA.eigenvalues rfl i : ℂ)*U v i :=
    hA.eigenvectorBasis_apply_self_apply rfl v i
  change U (A v) i+((t : ℂ)*Complex.I)*U v i=U b i at hv
  rw [hd] at hv
  apply (eq_div_iff hn).mpr
  simpa only [add_mul, mul_comm] using hv

/-- Parseval for the actual shifted inverse; no inverse coefficient is supplied. -/
theorem imaginaryShift_inverse_norm_sq (A : E →L[ℂ] E)
    (hA : A.toLinearMap.IsSymmetric) {t : ℝ} (ht : 0 < t) (b : E) :
    ‖Ring.inverse (imaginaryShift A t) b‖^2 =
      ∑ i, ‖(hA.eigenvectorBasis rfl).repr b i‖^2 / ((hA.eigenvalues rfl i)^2+t^2) := by
  rw [← (hA.eigenvectorBasis rfl).repr.norm_map (Ring.inverse (imaginaryShift A t) b),
    EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  rw [imaginaryShift_inverse_coordinates A hA ht b i, norm_div, div_pow]
  congr 1
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  ring

/-- Kernel overlap of the actual three-label graph equals t times the norm
of the imaginary-resolvent solution, without any data invertibility premise. -/
theorem blockGraph_projection_norm_sq (A : E →L[ℂ] E)
    (hA : A.toLinearMap.IsSymmetric) {t : ℝ} (ht : 0 < t) (b : E) :
    ‖(LinearMap.ker (blockAuxiliary A t).toLinearMap).starProjection (blockTriple 0 b 0)‖^2 =
      t^2*‖Ring.inverse (imaginaryShift A t) b‖^2 := by
  let U := (hA.eigenvectorBasis rfl).repr
  let a := hA.eigenvalues rfl
  have hd : ∀ x i, U (A x) i=(a i : ℂ)*U x i :=
    fun x i => hA.eigenvectorBasis_apply_self_apply rfl x i
  rw [original_kernel_projection U A a hd ht]
  simp only [conjugate_apply, LinearIsometryEquiv.norm_map, tripleCoordinates_blockTriple,
    map_zero]
  rw [kernelProjector_input_norm_sq a ht, imaginaryShift_inverse_norm_sq A hA ht b,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change t^2/(a i^2+t^2)*‖U b i‖^2=t^2*(‖U b i‖^2/(a i^2+t^2))
  ring

/-- The actual graph pseudoinverse norm is dominated by the same regularized
solution norm, for arbitrary singular Hermitian data. -/
theorem blockGraph_pseudoInverse_norm_le (A : E →L[ℂ] E)
    (hA : A.toLinearMap.IsSymmetric) {t : ℝ} (ht : 0 < t) (b : E) :
    ‖auxiliaryPseudoInverse A hA t (blockTriple 0 b 0)‖ ≤
      ‖Ring.inverse (imaginaryShift A t) b‖ := by
  let U := (hA.eigenvectorBasis rfl).repr
  let a := hA.eigenvalues rfl
  change ‖conjugate (tripleCoordinates U) (pseudoInverse a t) (blockTriple 0 b 0)‖ ≤ _
  simp only [conjugate_apply, LinearIsometryEquiv.norm_map, tripleCoordinates_blockTriple,
    map_zero, pseudoInverse_input]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [triple_norm_sq, norm_zero, zero_pow (by decide : 2≠0), add_zero, add_zero,
    imaginaryShift_inverse_norm_sq A hA ht b]
  have heq : (fun i => (a i : ℂ)/((a i : ℂ)^2+(t : ℂ)^2)) =
      fun i => ((a i/(a i^2+t^2) : ℝ) : ℂ) := by ext i; push_cast; rfl
  rw [heq, diagonal_real_norm_sq]
  apply Finset.sum_le_sum
  intro i _
  change (a i/(a i^2+t^2))^2*‖U b i‖^2 ≤ ‖U b i‖^2/(a i^2+t^2)
  have hd : 0 < a i^2+t^2 := by positivity
  have hcoef : (a i/(a i^2+t^2))^2 ≤ 1/(a i^2+t^2) := by
    rw [div_pow]
    apply (div_le_div_iff₀ (sq_pos_of_pos hd) hd).mpr
    nlinarith [sq_nonneg t]
  have hm := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖U b i‖)
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hm

/-- Logical spectral gap bound for the regularized solution. -/
theorem regularized_solution_gap_bound (A : E →L[ℂ] E)
    (hA : A.toLinearMap.IsSymmetric) (hunit : IsUnit A)
    {κ t : ℝ} (hκ : 0 ≤ κ) (ht : 0 < t) (hinv : ‖Ring.inverse A‖ ≤ κ) (b : E) :
    (1+κ^2*t^2)*‖Ring.inverse (imaginaryShift A t) b‖^2 ≤ κ^2*‖b‖^2 := by
  let v := Ring.inverse (imaginaryShift A t) b
  have he := imaginaryShift_norm_sq A hA t v
  rw [Perturbation.apply_inverse _ (imaginaryShift_isUnit A hA ht)] at he
  have hi : Ring.inverse A (A v)=v :=
    congrArg (fun T : E →L[ℂ] E => T v) (Ring.inverse_mul_cancel A hunit)
  have hv : ‖v‖ ≤ κ*‖A v‖ := by
    calc
      _ = ‖Ring.inverse A (A v)‖ := by rw [hi]
      _ ≤ ‖Ring.inverse A‖*‖A v‖ := (Ring.inverse A).le_opNorm _
      _ ≤ κ*‖A v‖ := mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hκ (norm_nonneg _))).mpr hv
  change (1+κ^2*t^2)*‖v‖^2 ≤ _
  nlinarith [congrArg (fun r : ℝ => κ^2*r) he]

end OptimalQLS.PhysicalRobustness
