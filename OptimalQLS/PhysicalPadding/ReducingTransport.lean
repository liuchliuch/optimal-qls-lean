import OptimalQLS.GraphEncoding.Geometry
import OptimalQLS.Krylov
import OptimalQLS.PolynomialTransform.Spectral
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Functional calculus on a reducing isometric copy

These lemmas transport the actual orthogonal kernel projection and the canonical
Hermitian Moore–Penrose inverse.  Both intertwining directions are explicit, so
an arbitrary operator on the orthogonal complement cannot affect the result.
-/

noncomputable section
namespace OptimalQLS.PhysicalPadding

open Polynomial PolynomialTransform

section Isometry
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- An isometric embedding preserves literal vector errors. -/
theorem isometry_norm_sub (J : E →ₗᵢ[ℂ] F) (x y : E) :
    ‖J x - J y‖ = ‖x - y‖ := by
  rw [← map_sub, J.norm_map]

/-- Normalization commutes with an isometry, including on the zero vector. -/
theorem isometry_normalize (J : E →ₗᵢ[ℂ] F) (x : E) :
    NormedSpace.normalize (J x) = J (NormedSpace.normalize x) := by
  unfold NormedSpace.normalize
  rw [J.norm_map]
  exact ((J.toLinearMap.restrictScalars ℝ).map_smul _ _).symm

/-- Normalized-state errors are unchanged by physical zero-padding. -/
theorem isometry_normalize_norm_sub (J : E →ₗᵢ[ℂ] F) (x y : E) :
    ‖NormedSpace.normalize (J x) - NormedSpace.normalize (J y)‖ =
      ‖NormedSpace.normalize x - NormedSpace.normalize y‖ := by
  rw [isometry_normalize, isometry_normalize, isometry_norm_sub]

end Isometry

section Hilbert
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- A reducing isometry commutes with the actual orthogonal kernel projection. -/
theorem reducing_kernel_projection
    (J : E →ₗᵢ[ℂ] F) (R : F →L[ℂ] E)
    (H : F →L[ℂ] F) (T : E →L[ℂ] E)
    (hinner : ∀ x y, inner ℂ (J x) y = inner ℂ x (R y))
    (hJ : ∀ x, H (J x) = J (T x))
    (hR : ∀ y, R (H y) = T (R y)) (x : E) :
    (LinearMap.ker H.toLinearMap).starProjection (J x) =
      J ((LinearMap.ker T.toLinearMap).starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · change H (J _) = 0
    rw [hJ]
    have hh := (LinearMap.ker T.toLinearMap).starProjection_apply_mem x
    change T _ = 0 at hh
    rw [hh, map_zero]
  · intro w hw
    have hw' : R w ∈ LinearMap.ker T.toLinearMap := by
      change T (R w) = 0
      rw [← hR]
      change H w = 0 at hw
      rw [hw, map_zero]
    rw [← map_sub, hinner]
    exact (LinearMap.ker T.toLinearMap).starProjection_inner_eq_zero x _ hw'

/-- The canonical spectral Moore–Penrose inverse commutes with a reducing
isometry; no inverse certificate or assumed pseudoinverse formula is used. -/
theorem reducing_pseudoInverse
    (J : E →ₗᵢ[ℂ] F) (R : F →L[ℂ] E)
    (H : F →L[ℂ] F) (T : E →L[ℂ] E)
    (hinner : ∀ x y, inner ℂ (J x) y = inner ℂ x (R y))
    (hJ : ∀ x, H (J x) = J (T x))
    (hR : ∀ y, R (H y) = T (R y))
    (hH : H.toLinearMap.IsSymmetric) (hT : T.toLinearMap.IsSymmetric) (x : E) :
    hermitianPseudoInverse H hH (J x) = J (hermitianPseudoInverse T hT x) := by
  let y := hermitianPseudoInverse H hH (J x) - J (hermitianPseudoInverse T hT x)
  have hy : y ∈ LinearMap.ker H.toLinearMap := by
    have hp := congrArg (fun C : F →L[ℂ] F => C (J x))
      (hermitian_mul_pseudoInverse H hH)
    have ht := congrArg (fun C : E →L[ℂ] E => C x)
      (hermitian_mul_pseudoInverse T hT)
    change H (hermitianPseudoInverse H hH (J x)) =
      J x - (LinearMap.ker H.toLinearMap).starProjection (J x) at hp
    change T (hermitianPseudoInverse T hT x) =
      x - (LinearMap.ker T.toLinearMap).starProjection x at ht
    change H (hermitianPseudoInverse H hH (J x) -
      J (hermitianPseudoInverse T hT x)) = 0
    rw [map_sub, hp, hJ, ht, map_sub,
      reducing_kernel_projection J R H T hinner hJ hR]
    simp
  have hrest : R y ∈ LinearMap.ker T.toLinearMap := by
    change T (R y) = 0
    change H y = 0 at hy
    rw [← hR, hy, map_zero]
  have hi : inner ℂ y y = 0 := by
    change inner ℂ (hermitianPseudoInverse H hH (J x) -
      J (hermitianPseudoInverse T hT x)) y = 0
    rw [inner_sub_left, GraphEncoding.pseudoInverse_inner_kernel H hH _ _ hy,
      hinner, GraphEncoding.pseudoInverse_inner_kernel T hT _ _ hrest]
    simp
  exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℂ)).mp hi)

/-- On an invertible Hermitian operator the canonical pseudoinverse is the
ordinary ring inverse, derived directly from its Moore–Penrose equation. -/
theorem hermitianPseudoInverse_eq_inverse (T : E →L[ℂ] E)
    (hT : T.toLinearMap.IsSymmetric) (hunit : IsUnit T) :
    hermitianPseudoInverse T hT = Ring.inverse T := by
  have h := (hermitianPseudoInverse_moore_penrose T hT).1
  calc
    hermitianPseudoInverse T hT =
        ((Ring.inverse T * T) * hermitianPseudoInverse T hT) * (T * Ring.inverse T) := by
      rw [Ring.inverse_mul_cancel _ hunit, Ring.mul_inverse_cancel _ hunit,
        one_mul, mul_one]
    _ = Ring.inverse T * (T * hermitianPseudoInverse T hT * T) * Ring.inverse T := by
      simp only [mul_assoc]
    _ = Ring.inverse T * T * Ring.inverse T := by rw [h]
    _ = Ring.inverse T := by rw [Ring.inverse_mul_cancel _ hunit, one_mul]

/-- Only the active operator needs to be invertible for its inverse to be
transported to the canonical pseudoinverse of a possibly singular padding. -/
theorem reducing_pseudoInverse_eq_inverse
    (J : E →ₗᵢ[ℂ] F) (R : F →L[ℂ] E)
    (H : F →L[ℂ] F) (T : E →L[ℂ] E)
    (hinner : ∀ x y, inner ℂ (J x) y = inner ℂ x (R y))
    (hJ : ∀ x, H (J x) = J (T x))
    (hR : ∀ y, R (H y) = T (R y))
    (hH : H.toLinearMap.IsSymmetric) (hT : T.toLinearMap.IsSymmetric)
    (hunit : IsUnit T) (x : E) :
    hermitianPseudoInverse H hH (J x) = J (Ring.inverse T x) := by
  rw [reducing_pseudoInverse J R H T hinner hJ hR hH hT,
    hermitianPseudoInverse_eq_inverse T hT hunit]

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
/-- Intertwining transports every nonnegative integer power. -/
theorem intertwining_pow (J : E →ₗᵢ[ℂ] F)
    (H : F →L[ℂ] F) (T : E →L[ℂ] E)
    (hJ : ∀ x, H (J x) = J (T x)) (n : ℕ) (x : E) :
    (H ^ n) (J x) = J ((T ^ n) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ', ContinuousLinearMap.mul_apply]
    rw [ih, hJ]

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
/-- Transport for the literal real-polynomial functional calculus. -/
theorem intertwining_polynomialOperator (J : E →ₗᵢ[ℂ] F)
    (H : F →L[ℂ] F) (T : E →L[ℂ] E)
    (hJ : ∀ x, H (J x) = J (T x)) (p : ℝ[X]) (x : E) :
    polynomialOperator p H (J x) = J (polynomialOperator p T x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [polynomialOperator, map_add, ContinuousLinearMap.add_apply] at *
    exact congrArg₂ (· + ·) hp hq
  | monomial n r =>
    simp only [polynomialOperator, Polynomial.aeval_monomial]
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ),
      RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul,
      intertwining_pow J H T hJ]

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
/-- A polynomial's error on an embedded input is exactly its active-space
error; nothing is asserted about the unused orthogonal complement. -/
theorem intertwining_polynomialOperator_error_eq (J : E →ₗᵢ[ℂ] F)
    (H : F →L[ℂ] F) (T S : E →L[ℂ] E)
    (hJ : ∀ x, H (J x) = J (T x)) (p : ℝ[X]) (x : E) :
    ‖polynomialOperator p H (J x) - J (S x)‖ =
      ‖(polynomialOperator p T - S) x‖ := by
  rw [intertwining_polynomialOperator J H T hJ, isometry_norm_sub]
  rfl

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
/-- An active operator-norm estimate gives the same physical input-state
estimate, without any global inverse or global error estimate. -/
theorem intertwining_polynomialOperator_error_le (J : E →ₗᵢ[ℂ] F)
    (H : F →L[ℂ] F) (T S : E →L[ℂ] E)
    (hJ : ∀ x, H (J x) = J (T x)) (p : ℝ[X]) {ε : ℝ}
    (herr : ‖polynomialOperator p T - S‖ ≤ ε) (x : E) :
    ‖polynomialOperator p H (J x) - J (S x)‖ ≤ ε * ‖x‖ := by
  rw [intertwining_polynomialOperator_error_eq J H T S hJ]
  exact ((polynomialOperator p T - S).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right herr (norm_nonneg x))

/-- A small-space kernel-filter estimate transports to the actual physical
kernel projector on every active input. -/
theorem reducing_polynomial_kernel_error_le
    (J : E →ₗᵢ[ℂ] F) (R : F →L[ℂ] E)
    (H : F →L[ℂ] F) (T : E →L[ℂ] E)
    (hinner : ∀ x y, inner ℂ (J x) y = inner ℂ x (R y))
    (hJ : ∀ x, H (J x) = J (T x))
    (hR : ∀ y, R (H y) = T (R y)) (p : ℝ[X]) {ε : ℝ}
    (herr : ‖polynomialOperator p T - (LinearMap.ker T.toLinearMap).starProjection‖ ≤ ε)
    (x : E) :
    ‖polynomialOperator p H (J x) - (LinearMap.ker H.toLinearMap).starProjection (J x)‖ ≤
      ε * ‖x‖ := by
  rw [reducing_kernel_projection J R H T hinner hJ hR]
  exact intertwining_polynomialOperator_error_le J H T _ hJ p herr x

/-- A small-space inverse-filter estimate transports to the genuine physical
pseudoinverse on active inputs even if the physical operator is singular. -/
theorem reducing_polynomial_pseudoInverse_error_le
    (J : E →ₗᵢ[ℂ] F) (R : F →L[ℂ] E)
    (H : F →L[ℂ] F) (T : E →L[ℂ] E)
    (hinner : ∀ x y, inner ℂ (J x) y = inner ℂ x (R y))
    (hJ : ∀ x, H (J x) = J (T x))
    (hR : ∀ y, R (H y) = T (R y))
    (hH : H.toLinearMap.IsSymmetric) (hT : T.toLinearMap.IsSymmetric)
    (p : ℝ[X]) {ε : ℝ}
    (herr : ‖polynomialOperator p T - hermitianPseudoInverse T hT‖ ≤ ε) (x : E) :
    ‖polynomialOperator p H (J x) - hermitianPseudoInverse H hH (J x)‖ ≤ ε * ‖x‖ := by
  rw [reducing_pseudoInverse J R H T hinner hJ hR hH hT]
  exact intertwining_polynomialOperator_error_le J H T _ hJ p herr x

end Hilbert

section RealModule
variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- Algebraic powers commute with an intertwining linear map. -/
theorem linearMap_intertwining_pow (J : E →ₗ[ℝ] F)
    (H : Module.End ℝ F) (T : Module.End ℝ E)
    (hJ : ∀ x, H (J x) = J (T x)) (n : ℕ) (x : E) :
    (H ^ n) (J x) = J ((T ^ n) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ', Module.End.mul_apply]
    rw [ih, hJ]

/-- The entire real Krylov space is the image of the unpadded Krylov space. -/
theorem intertwining_realKrylov (J : E →ₗ[ℝ] F)
    (H : Module.End ℝ F) (T : Module.End ℝ E)
    (hJ : ∀ x, H (J x) = J (T x)) (x : E) :
    (realKrylov T x).map J = realKrylov H (J x) := by
  unfold realKrylov
  rw [Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨z, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, linearMap_intertwining_pow J H T hJ n x⟩
  · rintro ⟨n, rfl⟩
    exact ⟨(T ^ n) x, ⟨n, rfl⟩, (linearMap_intertwining_pow J H T hJ n x).symm⟩

/-- In particular, no Krylov iterate can leave the range of the embedding. -/
theorem realKrylov_le_range (J : E →ₗ[ℝ] F)
    (H : Module.End ℝ F) (T : Module.End ℝ E)
    (hJ : ∀ x, H (J x) = J (T x)) (x : E) :
    realKrylov H (J x) ≤ LinearMap.range J := by
  rw [← intertwining_realKrylov J H T hJ]
  rintro y ⟨z, _, rfl⟩
  exact ⟨z, rfl⟩

end RealModule

section HilbertKrylov
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Real-coefficient Hermitian Krylov spaces transport exactly. -/
theorem intertwining_hermitianKrylov (J : E →ₗᵢ[ℂ] F)
    (H : F →L[ℂ] F) (T : E →L[ℂ] E)
    (hJ : ∀ x, H (J x) = J (T x)) (x : E) :
    (hermitianKrylov T x).map (J.toLinearMap.restrictScalars ℝ) =
      hermitianKrylov H (J x) :=
  intertwining_realKrylov (J.toLinearMap.restrictScalars ℝ)
    (H.toLinearMap.restrictScalars ℝ) (T.toLinearMap.restrictScalars ℝ) hJ x

/-- A Krylov vector started in an isometric copy stays in its actual range. -/
theorem hermitianKrylov_le_range (J : E →ₗᵢ[ℂ] F)
    (H : F →L[ℂ] F) (T : E →L[ℂ] E)
    (hJ : ∀ x, H (J x) = J (T x)) (x : E) :
    hermitianKrylov H (J x) ≤ LinearMap.range (J.toLinearMap.restrictScalars ℝ) :=
  realKrylov_le_range (J.toLinearMap.restrictScalars ℝ)
    (H.toLinearMap.restrictScalars ℝ) (T.toLinearMap.restrictScalars ℝ) hJ x

end HilbertKrylov
end OptimalQLS.PhysicalPadding
