import OptimalQLS.Geometry.SpectralPromises
import OptimalQLS.PolynomialTransform.ChebyshevFilter
import OptimalQLS.PolynomialTransform.CorrectionPolynomial
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Polynomial functional calculus in actual Hilbert-space coordinates

These are analytic statements about the literal polynomial of the original
operator. They do not postulate an implementing oracle circuit.
-/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Polynomial
open Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
variable {ι : Type*} [Fintype ι]

/-- Ordinary polynomial functional calculus in the endomorphism algebra. -/
def polynomialOperator (p : ℝ[X]) (A : E →L[ℂ] E) : E →L[ℂ] E :=
  Polynomial.aeval A p

omit [FiniteDimensional ℂ E] in
theorem pow_coordinates (U : E ≃ₗᵢ[ℂ] Vec ι) (A : E →L[ℂ] E)
    (a : ι → ℝ) (hdiag : ∀ x i, U (A x) i = (a i : ℂ) * U x i)
    (n : ℕ) (x : E) (i : ι) :
    U ((A ^ n) x) i = (a i : ℂ) ^ n * U x i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, hdiag, ih, pow_succ']
    ring

/-- Polynomial evaluation commutes with the derived orthonormal coordinates. -/
theorem polynomial_coordinates (U : E ≃ₗᵢ[ℂ] Vec ι) (A : E →L[ℂ] E)
    (a : ι → ℝ) (hdiag : ∀ x i, U (A x) i = (a i : ℂ) * U x i)
    (p : ℝ[X]) (x : E) (i : ι) :
    U (polynomialOperator p A x) i = ((p.eval (a i) : ℝ) : ℂ) * U x i := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [polynomialOperator, map_add, ContinuousLinearMap.add_apply,
      PiLp.add_apply, eval_add, Complex.ofReal_add, add_mul] at *
    exact congrArg₂ (· + ·) hp hq
  | monomial n r =>
    simp only [polynomialOperator, aeval_monomial, eval_monomial]
    rw [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.mul_apply]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
    simp only [PiLp.smul_apply, smul_eq_mul, pow_coordinates U A a hdiag,
      Complex.ofReal_mul, Complex.ofReal_pow]
    change (r : ℂ) * ((a i : ℂ) ^ n * U x i) =
      ((r : ℂ) * (a i : ℂ) ^ n) * U x i
    ring

theorem polynomialOperator_eq_conjugate (U : E ≃ₗᵢ[ℂ] Vec ι) (A : E →L[ℂ] E)
    (a : ι → ℝ) (hdiag : ∀ x i, U (A x) i = (a i : ℂ) * U x i) (p : ℝ[X]) :
    polynomialOperator p A = conjugate U (diagonal (fun i => ((p.eval (a i) : ℝ) : ℂ))) :=
  operator_eq_conjugate U _ _ (fun x i => polynomial_coordinates U A a hdiag p x i)

/-- Uniform scalar bounds imply an actual Euclidean operator-norm bound. -/
theorem polynomialOperator_norm_le (U : E ≃ₗᵢ[ℂ] Vec ι) (A : E →L[ℂ] E)
    (a : ι → ℝ) (hdiag : ∀ x i, U (A x) i = (a i : ℂ) * U x i)
    (p : ℝ[X]) {M : ℝ} (hM : 0 ≤ M) (hp : ∀ i, |p.eval (a i)| ≤ M) :
    ‖polynomialOperator p A‖ ≤ M := by
  rw [polynomialOperator_eq_conjugate U A a hdiag]
  exact conjugate_opNorm_le U _ hM (diagonal_real_opNorm_le _ hM hp)

/-- The literal orthogonal projection onto the zero eigencoordinates. -/
def zeroIndicator (a : ι → ℝ) (i : ι) : ℝ := if a i = 0 then 1 else 0

theorem diagonal_kernel_projection (a : ι → ℝ) :
    (LinearMap.ker (diagonal (fun i => (a i : ℂ))).toLinearMap).starProjection =
      diagonal (fun i => (zeroIndicator a i : ℂ)) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · change diagonal (fun i => (a i : ℂ)) (diagonal (fun i => (zeroIndicator a i : ℂ)) x) = 0
    ext i
    by_cases h : a i = 0 <;> simp [zeroIndicator, h]
  · intro w hw
    change diagonal (fun i => (a i : ℂ)) w = 0 at hw
    simp only [PiLp.inner_apply]
    apply Finset.sum_eq_zero
    intro i _
    by_cases h : a i = 0
    · simp [zeroIndicator, h]
    · have hwi : w i = 0 := by
        have hi := congrArg (fun v : Vec ι => v i) hw
        have hai : (a i : ℂ) ≠ 0 := by exact_mod_cast h
        exact (mul_eq_zero.mp (by simpa using hi)).resolve_left hai
      simp [hwi]

/-- The actual kernel projection in the original basis. -/
theorem kernel_projection_coordinates (U : E ≃ₗᵢ[ℂ] Vec ι) (A : E →L[ℂ] E)
    (a : ι → ℝ) (hdiag : ∀ x i, U (A x) i = (a i : ℂ) * U x i) :
    (LinearMap.ker A.toLinearMap).starProjection =
      conjugate U (diagonal (fun i => (zeroIndicator a i : ℂ))) := by
  rw [operator_eq_conjugate U A a hdiag, ← conjugate_kernel_projection,
    diagonal_kernel_projection]

/-- The spectral estimate is about p(A) and mathlib's kernel projection,
not an abstract error variable or an assumed certificate. -/
theorem polynomial_kernel_distance (U : E ≃ₗᵢ[ℂ] Vec ι) (A : E →L[ℂ] E)
    (a : ι → ℝ) (hdiag : ∀ x i, U (A x) i = (a i : ℂ) * U x i)
    (p : ℝ[X]) (hp0 : p.eval 0 = 1) {η : ℝ} (hη : 0 ≤ η)
    (hp : ∀ i, a i ≠ 0 → |p.eval (a i)| ≤ η) :
    ‖polynomialOperator p A - (LinearMap.ker A.toLinearMap).starProjection‖ ≤ η := by
  rw [polynomialOperator_eq_conjugate U A a hdiag,
    kernel_projection_coordinates U A a hdiag, ← map_sub]
  have heq : diagonal (fun i => ((p.eval (a i) : ℝ) : ℂ)) -
      diagonal (fun i => (zeroIndicator a i : ℂ)) =
      diagonal (fun i => ((p.eval (a i) - zeroIndicator a i : ℝ) : ℂ)) := by
    ext x i
    simp
    ring
  rw [heq]
  apply conjugate_opNorm_le U _ hη
  apply diagonal_real_opNorm_le _ hη
  intro i
  by_cases hi : a i = 0
  · simp [zeroIndicator, hi, hp0, hη]
  · simpa [zeroIndicator, hi] using hp i hi

/-- Full scalar-to-operator filtering, with real orthonormal coordinates
derived from Hermiticity rather than supplied as a promise. -/
theorem kernelFilter_operator_bound (A : E →L[ℂ] E) (hA : A.toLinearMap.IsSymmetric)
    {δ η : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / Real.sqrt 12)
    (hη0 : 0 < η) (hη1 : η < 1 / 2)
    (hspec : ∀ μ : ℂ, μ ∈ spectrum ℂ A.toLinearMap → μ ≠ 0 → δ ≤ ‖μ‖ ∧ ‖μ‖ ≤ 1) :
    ‖polynomialOperator (kernelFilter δ η) A -
      (LinearMap.ker A.toLinearMap).starProjection‖ ≤ η := by
  let U := (hA.eigenvectorBasis rfl).repr
  let a := hA.eigenvalues rfl
  have hdiag : ∀ x i, U (A x) i = (a i : ℂ) * U x i :=
    fun x i => hA.eigenvectorBasis_apply_self_apply rfl x i
  apply polynomial_kernel_distance U A a hdiag _
    (lemma51_kernel_filter hδ0 hδ1 hη0 hη1).2.2.1 hη0.le
  intro i hi
  have he := Module.End.hasEigenvalue_of_hasEigenvector
    (hA.hasEigenvector_eigenvectorBasis rfl i)
  have hi' : (a i : ℂ) ≠ 0 := by exact_mod_cast hi
  have hb := hspec _ he.mem_spectrum hi'
  have hb' : δ ≤ |a i| ∧ |a i| ≤ 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hb
  exact kernelFilter_tail hδ0 hδ1 hη0 hb'.1 hb'.2

/-- Scalar approximation is transported to the original-coordinate operator. -/
theorem polynomial_diagonal_distance (U : E ≃ₗᵢ[ℂ] Vec ι) (A : E →L[ℂ] E)
    (a : ι → ℝ) (hdiag : ∀ x i, U (A x) i = (a i : ℂ) * U x i)
    (p : ℝ[X]) (f : ι → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hp : ∀ i, |p.eval (a i) - f i| ≤ M) :
    ‖polynomialOperator p A - conjugate U (diagonal (fun i => (f i : ℂ)))‖ ≤ M := by
  rw [polynomialOperator_eq_conjugate U A a hdiag, ← map_sub]
  have heq : diagonal (fun i => ((p.eval (a i) : ℝ) : ℂ)) -
      diagonal (fun i => (f i : ℂ)) =
      diagonal (fun i => ((p.eval (a i) - f i : ℝ) : ℂ)) := by
    ext x i
    simp
    ring
  rw [heq]
  exact conjugate_opNorm_le U _ hM (diagonal_real_opNorm_le _ hM hp)

/-- The actual inverse-based correction operator in Lemma 5.5. -/
def idealCorrection (A : E →L[ℂ] E) (κ : ℝ) : E →L[ℂ] E :=
  (1 / 4 : ℂ) • (1 + ((κ⁻¹)^2 : ℂ) • (Ring.inverse A)^2)

/-- The analytic part of Lemma 5.5, evaluated on the actual input operator.
The scalar inverse-square approximant is not assumed to have a circuit. -/
theorem correctionOperator_distance (A : E →L[ℂ] E)
    (hA : A.toLinearMap.IsSymmetric) (hunit : IsUnit A)
    {κ η : ℝ} (hκ : 0 < κ) (hAnorm : ‖A‖ ≤ 1) (hinorm : ‖Ring.inverse A‖ ≤ κ)
    (hη : 0 ≤ η) (p : ℝ[X])
    (hp : ∀ x : ℝ, κ⁻¹ ≤ |x| → |x| ≤ 1 →
      |p.eval x - (κ⁻¹)^2 / (2 * x^2)| ≤ η) :
    ‖polynomialOperator (correctionPolynomial p) A - idealCorrection A κ‖ ≤ η / 2 := by
  let U := (hA.eigenvectorBasis rfl).repr
  let a := hA.eigenvalues rfl
  have hdiag : ∀ x i, U (A x) i = (a i : ℂ) * U x i :=
    fun x i => hA.eigenvectorBasis_apply_self_apply rfl x i
  have ha : ∀ i, κ⁻¹ ≤ |a i| ∧ |a i| ≤ 1 := fun i =>
    spectral_coordinate_bounds A hA hunit hκ hAnorm hinorm i
  have hane : ∀ i, a i ≠ 0 := by
    intro i hi
    have hi0 := (ha i).1
    rw [hi, abs_zero] at hi0
    exact (not_le_of_gt (inv_pos.mpr hκ)) hi0
  have hinv := (inverse_from_coordinates U A a hdiag hane).2
  have hc : 1 + ((κ⁻¹)^2 : ℂ) • (Ring.inverse A)^2 =
      conjugate U (diagonal (fun i => ((1 + (κ⁻¹)^2 / a i ^ 2 : ℝ) : ℂ))) := by
    rw [correction_operator_formula, map_add, map_one, conjugate_smul, map_pow, ← hinv]
  have hideal : idealCorrection A κ = conjugate U
      (diagonal (fun i => (((1 + (κ⁻¹)^2 / a i ^ 2) / 4 : ℝ) : ℂ))) := by
    rw [idealCorrection, hc, ← conjugate_smul]
    congr 1
    ext x i
    simp
    ring
  rw [hideal]
  apply polynomial_diagonal_distance U A a hdiag _ _ (by positivity)
  intro i
  exact correctionPolynomial_error (hp (a i) (ha i).1 (ha i).2)

/-- The 3/4 global correction bound also holds in the actual operator norm. -/
theorem correctionOperator_norm_le (A : E →L[ℂ] E) (hA : A.toLinearMap.IsSymmetric)
    (hAnorm : ‖A‖ ≤ 1) (p : ℝ[X])
    (hp : ∀ x : ℝ, |x| ≤ 1 → |p.eval x| ≤ 1) :
    ‖polynomialOperator (correctionPolynomial p) A‖ ≤ 3 / 4 := by
  let U := (hA.eigenvectorBasis rfl).repr
  let a := hA.eigenvalues rfl
  have hdiag : ∀ x i, U (A x) i = (a i : ℂ) * U x i :=
    fun x i => hA.eigenvectorBasis_apply_self_apply rfl x i
  apply polynomialOperator_norm_le U A a hdiag _ (by norm_num)
  intro i
  apply correctionPolynomial_bounded
  apply hp
  let v := hA.eigenvectorBasis rfl i
  have hv : ‖v‖ = 1 := (hA.eigenvectorBasis rfl).orthonormal.norm_eq_one i
  have heig : A v = (a i : ℂ) • v :=
    Module.End.mem_eigenspace_iff.mp (hA.hasEigenvector_eigenvectorBasis rfl i).1
  have hn := A.le_opNorm v
  rw [heig, norm_smul, hv, mul_one, mul_one, Complex.norm_real, Real.norm_eq_abs] at hn
  exact hn.trans hAnorm

end OptimalQLS.PolynomialTransform
