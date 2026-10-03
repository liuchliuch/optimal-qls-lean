import QuantumChannelStein.TensorNorm
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Douglas matrix factorization

This file proves Lemma 3.2 by factoring the adjoint on its range and extending
that map using the orthogonal projection. No invertibility is required.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.Factorization

open scoped InnerProduct Matrix.Norms.L2Operator ComplexOrder

/-- A bounded map on the range of `G` extends to the whole Hilbert space with
no increase in its bound. This construction includes singular and zero maps. -/
theorem exists_left_factor_of_norm_le
    {H E K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [FiniteDimensional ℂ K]
    (F : H →L[ℂ] E) (G : H →L[ℂ] K) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x, ‖F x‖ ≤ c * ‖G x‖) :
    ∃ T : K →L[ℂ] E, F = T.comp G ∧ ‖T‖ ≤ c := by
  let g := G.toLinearMap
  let f := F.toLinearMap
  have hker : LinearMap.ker g ≤ LinearMap.ker f := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    have hxG : G x = 0 := LinearMap.mem_ker.mp hx
    simpa only [hxG, norm_zero, mul_zero] using h x
  let L : LinearMap.range g →ₗ[ℂ] E :=
    ((LinearMap.ker g).liftQ f hker).comp g.quotKerEquivRange.symm.toLinearMap
  have hL (x : H) : L ⟨g x, LinearMap.mem_range_self g x⟩ = f x := by
    simp [L]
  have hbound (y : LinearMap.range g) : ‖L y‖ ≤ c * ‖y‖ := by
    obtain ⟨x, hx⟩ := y.property
    have heq : y = ⟨g x, LinearMap.mem_range_self g x⟩ := Subtype.ext hx.symm
    rw [heq, hL]
    exact h x
  let Lc := L.mkContinuous c hbound
  let T := Lc.comp (LinearMap.range g).orthogonalProjection
  refine ⟨T, ?_, ?_⟩
  · ext x
    change f x = L ((LinearMap.range g).orthogonalProjection (g x))
    change f x = L ((LinearMap.range g).orthogonalProjection
      (⟨g x, LinearMap.mem_range_self g x⟩ : LinearMap.range g))
    rw [Submodule.orthogonalProjection_mem_subspace_eq_self]
    exact (hL x).symm
  · apply ContinuousLinearMap.opNorm_le_bound _ hc
    intro x
    exact (hbound _).trans (mul_le_mul_of_nonneg_left
      ((LinearMap.range g).norm_orthogonalProjection_apply_le x) hc)

/-- The adjoint form of the preceding extension theorem. -/
theorem exists_right_factor_of_adjoint_norm_le
    {H E K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
    (F : E →L[ℂ] H) (G : K →L[ℂ] H) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x, ‖F.adjoint x‖ ≤ c * ‖G.adjoint x‖) :
    ∃ D : E →L[ℂ] K, F = G.comp D ∧ ‖D‖ ≤ c := by
  obtain ⟨T, hT, hn⟩ := exists_left_factor_of_norm_le F.adjoint G.adjoint hc h
  refine ⟨T.adjoint, ?_, ?_⟩
  · simpa only [ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.adjoint_comp]
      using congrArg ContinuousLinearMap.adjoint hT
  · simpa using hn

open Matrix WithLp TensorNorm

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
  [DecidableEq m] [DecidableEq n] [DecidableEq k]

@[simp] theorem matrixMap_conjTranspose (A : Matrix m n ℂ) :
    matrixMap Aᴴ = (matrixMap A).adjoint := by
  change (Aᴴ.toEuclideanLin).toContinuousLinearMap = _
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact LinearMap.adjoint_toContinuousLinearMap _

/-- The quadratic form of a Gram matrix is the squared norm of its adjoint action. -/
theorem adjoint_norm_sq_eq_gram (A : Matrix m n ℂ) (x : EuclideanSpace ℂ m) :
    ‖matrixMap Aᴴ x‖ ^ 2 =
      (star (ofLp x) ⬝ᵥ ((A * Aᴴ) *ᵥ ofLp x)).re := by
  rw [matrixMap_conjTranspose,
    ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right,
    ContinuousLinearMap.adjoint_adjoint]
  rw [← matrixMap_conjTranspose, ← matrixMap_mul]
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rfl

/-- PSD domination of the Gram matrices bounds the adjoint action. -/
theorem adjoint_norm_le_of_gram_posSemidef (F : Matrix m n ℂ) (G : Matrix m k ℂ)
    {t : ℝ} (ht : 0 ≤ t) (h : (t • (G * Gᴴ) - F * Fᴴ).PosSemidef)
    (x : EuclideanSpace ℂ m) :
    ‖matrixMap Fᴴ x‖ ≤ Real.sqrt t * ‖matrixMap Gᴴ x‖ := by
  have hq := h.re_dotProduct_nonneg (ofLp x)
  have hsq : ‖matrixMap Fᴴ x‖ ^ 2 ≤ t * ‖matrixMap Gᴴ x‖ ^ 2 := by
    rw [adjoint_norm_sq_eq_gram, adjoint_norm_sq_eq_gram]
    simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec (R := ℝ), dotProduct_sub,
      dotProduct_smul, RCLike.re_to_complex, Complex.sub_re, Complex.real_smul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      sub_nonneg] using hq
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  simpa only [mul_pow, Real.sq_sqrt ht] using hsq

/-- **Lemma 3.2 (Matrix factorization).** If `F Fᴴ ≤ t G Gᴴ` in PSD order,
then `F = G D` for a rectangular matrix whose Hilbert operator norm is at most
`sqrt t`. All finite dimensions, including zero dimensions, are allowed. -/
theorem matrix_factorization (F : Matrix m n ℂ) (G : Matrix m k ℂ)
    {t : ℝ} (ht : 0 ≤ t) (h : (t • (G * Gᴴ) - F * Fᴴ).PosSemidef) :
    ∃ D : Matrix k n ℂ, F = G * D ∧ ‖D‖ ≤ Real.sqrt t := by
  have hn (x : EuclideanSpace ℂ m) :
      ‖(matrixMap F).adjoint x‖ ≤ Real.sqrt t * ‖(matrixMap G).adjoint x‖ := by
    simpa only [← matrixMap_conjTranspose] using
      adjoint_norm_le_of_gram_posSemidef F G ht h x
  obtain ⟨d, hd, hdn⟩ := exists_right_factor_of_adjoint_norm_le
    (matrixMap F) (matrixMap G) (Real.sqrt_nonneg t) hn
  let e : Matrix k n ℂ ≃ₗ[ℂ] (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ k) :=
    Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap
  let D := e.symm d
  have hD : matrixMap D = d := e.apply_symm_apply d
  refine ⟨D, ?_, ?_⟩
  · apply (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap).injective
    change matrixMap F = matrixMap (G * D)
    rw [matrixMap_mul, hD]
    exact hd
  · change ‖matrixMap D‖ ≤ Real.sqrt t
    rw [hD]
    exact hdn

end QuantumChannelStein.Factorization
