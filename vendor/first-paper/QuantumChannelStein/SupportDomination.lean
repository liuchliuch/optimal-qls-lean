import QuantumChannelStein.Factorization
import Mathlib.Analysis.Matrix.Order

/-!
# Finite support and positive-semidefinite domination

For finite complex positive-semidefinite matrices, kernel inclusion is
equivalent to domination by a finite scalar at least one. This is the operator
support prerequisite of Lemma 3.1; it does not assert relative-entropy claims.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SupportDomination

open scoped InnerProduct Matrix.Norms.L2Operator ComplexOrder MatrixOrder
open Matrix WithLp TensorNorm Factorization

/-- Kernel inclusion between finite-dimensional operators gives a finite
relative action bound, including when either operator is singular. -/
theorem exists_norm_bound_of_ker_le
    {H E K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [FiniteDimensional ℂ K]
    (F : H →L[ℂ] E) (G : H →L[ℂ] K)
    (hker : LinearMap.ker G.toLinearMap ≤ LinearMap.ker F.toLinearMap) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x, ‖F x‖ ≤ c * ‖G x‖ := by
  let g := G.toLinearMap
  let f := F.toLinearMap
  let L : LinearMap.range g →ₗ[ℂ] E :=
    ((LinearMap.ker g).liftQ f hker).comp g.quotKerEquivRange.symm.toLinearMap
  have hL (x : H) : L ⟨g x, LinearMap.mem_range_self g x⟩ = f x := by
    simp [L]
  let Lc : LinearMap.range g →L[ℂ] E := L.toContinuousLinearMap
  refine ⟨‖Lc‖, norm_nonneg Lc, fun x => ?_⟩
  have h := Lc.le_opNorm ⟨g x, LinearMap.mem_range_self g x⟩
  change ‖L ⟨g x, LinearMap.mem_range_self g x⟩‖ ≤ ‖Lc‖ * ‖g x‖ at h
  rw [hL] at h
  exact h

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- A Gram matrix and its defining factor have the same kernel. -/
theorem gram_mulVec_eq_zero_iff (F : Matrix n n ℂ) (x : n → ℂ) :
    (Fᴴ * F) *ᵥ x = 0 ↔ F *ᵥ x = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]⟩
  have hq : star x ⬝ᵥ ((Fᴴ * F) *ᵥ x) = 0 := by rw [h, dotProduct_zero]
  rw [← Matrix.mulVec_mulVec, dotProduct_mulVec _ _ (F *ᵥ x),
    vecMul_conjTranspose, star_star] at hq
  exact dotProduct_star_self_eq_zero.mp hq

/-- The real quadratic form of a Gram matrix is its factor's squared norm. -/
theorem norm_sq_eq_gram (F : Matrix n n ℂ) (x : EuclideanSpace ℂ n) :
    ‖matrixMap F x‖ ^ 2 = (star (ofLp x) ⬝ᵥ ((Fᴴ * F) *ᵥ ofLp x)).re := by
  simpa only [conjTranspose_conjTranspose] using adjoint_norm_sq_eq_gram Fᴴ x

omit [DecidableEq n] in
/-- Domination forces kernel inclusion. The scalar need not be positive for
this implication. -/
theorem ker_le_of_posSemidef_smul_sub {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) {c : ℝ} (h : (c • B - A).PosSemidef) :
    LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin := by
  intro x hx
  have hxB : B *ᵥ x = 0 := LinearMap.mem_ker.mp hx
  apply LinearMap.mem_ker.mpr
  apply (hA.dotProduct_mulVec_zero_iff x).mp
  have hneg : 0 ≤ -(star x ⬝ᵥ A *ᵥ x) := by
    simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, hxB, smul_zero,
      zero_sub, dotProduct_neg] using h.dotProduct_mulVec_nonneg x
  exact le_antisymm (neg_nonneg.mp hneg) (hA.dotProduct_mulVec_nonneg x)

/-- Kernel inclusion for two Gram factors yields finite PSD domination. -/
theorem exists_gram_domination (F G : Matrix n n ℂ)
    (hker : LinearMap.ker G.mulVecLin ≤ LinearMap.ker F.mulVecLin) :
    ∃ c : ℝ, 1 ≤ c ∧ (c • (Gᴴ * G) - Fᴴ * F).PosSemidef := by
  have hker' : LinearMap.ker (matrixMap G).toLinearMap ≤
      LinearMap.ker (matrixMap F).toLinearMap := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    have hxG : G *ᵥ ofLp x = 0 := by
      simpa only [ContinuousLinearMap.coe_coe, matrixMap_apply, toLp_eq_zero] using
        LinearMap.mem_ker.mp hx
    have hxF : F *ᵥ ofLp x = 0 :=
      LinearMap.mem_ker.mp (hker (LinearMap.mem_ker.mpr hxG))
    simp only [ContinuousLinearMap.coe_coe, matrixMap_apply, hxF, toLp_zero]
  obtain ⟨d, hd, hbound⟩ := exists_norm_bound_of_ker_le (matrixMap F) (matrixMap G) hker'
  let c : ℝ := max 1 (d ^ 2)
  have hc : 0 ≤ c := le_trans zero_le_one (le_max_left _ _)
  have hHerm : (c • (Gᴴ * G) - Fᴴ * F).IsHermitian :=
    ((posSemidef_conjTranspose_mul_self G).smul hc).isHermitian.sub
      (posSemidef_conjTranspose_mul_self F).isHermitian
  refine ⟨c, le_max_left _ _, Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm (fun x => ?_)⟩
  apply RCLike.nonneg_iff.mpr
  refine ⟨?_, hHerm.im_star_dotProduct_mulVec_self x⟩
  have hs : ‖matrixMap F (toLp 2 x)‖ ^ 2 ≤ c * ‖matrixMap G (toLp 2 x)‖ ^ 2 := by
    calc
      _ ≤ (d * ‖matrixMap G (toLp 2 x)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hbound (toLp 2 x)) 2
      _ = d ^ 2 * ‖matrixMap G (toLp 2 x)‖ ^ 2 := mul_pow _ _ _
      _ ≤ c * ‖matrixMap G (toLp 2 x)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
  rw [norm_sq_eq_gram, norm_sq_eq_gram] at hs
  simpa only [ofLp_toLp, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_smul, RCLike.re_to_complex, Complex.sub_re, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    sub_nonneg] using hs

/-- For finite PSD matrices, support inclusion gives domination by a scalar
at least one. Support inclusion is expressed as reversed kernel inclusion. -/
theorem exists_domination_of_ker_le {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hker : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin) :
    ∃ c : ℝ, 1 ≤ c ∧ (c • B - A).PosSemidef := by
  obtain ⟨F, hF⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  obtain ⟨G, hG⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  change A = Fᴴ * F at hF
  change B = Gᴴ * G at hG
  have hker' : LinearMap.ker G.mulVecLin ≤ LinearMap.ker F.mulVecLin := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    apply (gram_mulVec_eq_zero_iff F x).mp
    have hxG : G *ᵥ x = 0 := LinearMap.mem_ker.mp hx
    have hxB : B *ᵥ x = 0 := by
      rw [hG]
      exact (gram_mulVec_eq_zero_iff G x).mpr hxG
    have hxA : A *ᵥ x = 0 := LinearMap.mem_ker.mp (hker (LinearMap.mem_ker.mpr hxB))
    rwa [← hF]
  simpa only [← hF, ← hG] using exists_gram_domination F G hker'

/-- Finite support inclusion is equivalent to finite PSD domination.
This covers zero matrices and zero-dimensional spaces. -/
theorem ker_le_iff_exists_domination {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin ↔
      ∃ c : ℝ, 1 ≤ c ∧ (c • B - A).PosSemidef := by
  constructor
  · exact exists_domination_of_ker_le hA hB
  · rintro ⟨c, _, hc⟩
    exact ker_le_of_posSemidef_smul_sub hA hc

end QuantumChannelStein.SupportDomination
