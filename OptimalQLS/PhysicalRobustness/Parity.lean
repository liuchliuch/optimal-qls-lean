import OptimalQLS.PhysicalRobustness.SpectralCutoff
import OptimalQLS.LowerBounds.HermitianDilation
import OptimalQLS.MatrixPseudoInverse

/-! Odd spectral inversion reverses an anti-commuting sign grading. In
particular the truncated inverse of a Hermitian dilation sends the left
source exactly into the right data summand, preserving the sharp noise term
when the general-input algorithm performs its final extraction. -/
noncomputable section
namespace OptimalQLS.PhysicalRobustness
open Geometry Matrix LowerBounds

/-- The actual scalar spectral function used by highInverse. -/
def cutoffInverseValue (δ x : ℝ) : ℝ := if |x|≤δ then 0 else x⁻¹

theorem cutoffInverseValue_neg (δ x : ℝ) : cutoffInverseValue δ (-x) = -cutoffInverseValue δ x := by
  simp only [cutoffInverseValue,abs_neg]
  split_ifs <;> simp

section Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- Functional calculus on any eigenvector, not just the chosen basis. -/
theorem highInverse_apply_eigenvector (B : E →L[ℂ] E) (hB : B.toLinearMap.IsSymmetric)
    (δ μ : ℝ) (v : E) (he : B v=(μ : ℂ) • v) :
    highInverse B hB δ v=(cutoffInverseValue δ μ : ℂ) • v := by
  let U := (hB.eigenvectorBasis rfl).repr
  let a := hB.eigenvalues rfl
  apply U.injective
  ext i
  have hc := congrArg (fun x : E => U x i) he
  have hd : U (B v) i=(a i : ℂ)*U v i := hB.eigenvectorBasis_apply_self_apply rfl v i
  change U (B v) i=U ((μ : ℂ) • v) i at hc
  rw [hd,map_smul] at hc
  change (a i : ℂ)*U v i=(μ : ℂ)*U v i at hc
  have hout : U (highInverse B hB δ v) i=
      (if |a i|≤δ then (0:ℂ) else ((a i)⁻¹ : ℝ))*U v i := by
    simp [highInverse,U,a,conjugate_apply]
  rw [hout,map_smul]
  change (if |a i|≤δ then (0:ℂ) else ((a i)⁻¹ : ℝ))*U v i=
    (cutoffInverseValue δ μ : ℂ)*U v i
  by_cases hi : U v i=0
  · simp [hi]
  · have ha : a i=μ := Complex.ofReal_injective (mul_right_cancel₀ hi hc)
    rw [ha]
    by_cases hm : |μ|≤δ <;> simp [cutoffInverseValue,hm]

/-- Odd cutoff inversion inherits anti-commutation with an arbitrary linear
sign operator. No invertibility of B or high-subspace certificate is required. -/
theorem highInverse_anticommutes (B Z : E →L[ℂ] E) (hB : B.toLinearMap.IsSymmetric)
    (δ : ℝ) (hanti : ∀ x, Z (B x) = -B (Z x)) :
    Z*highInverse B hB δ = -(highInverse B hB δ)*Z := by
  have hlin : (Z*highInverse B hB δ).toLinearMap =
      (-(highInverse B hB δ)*Z).toLinearMap := by
    apply (hB.eigenvectorBasis rfl).toBasis.ext
    intro i
    let v := hB.eigenvectorBasis rfl i
    let μ := hB.eigenvalues rfl i
    have he : B v=(μ : ℂ) • v :=
      Module.End.mem_eigenspace_iff.mp (hB.hasEigenvector_eigenvectorBasis rfl i).1
    have hz : B (Z v)=((-μ : ℝ) : ℂ) • Z v := by
      calc
        _ = -Z (B v) := by rw [hanti,neg_neg]
        _ = _ := by rw [he,map_smul]; simp
    change Z (highInverse B hB δ v)= -highInverse B hB δ (Z v)
    rw [highInverse_apply_eigenvector B hB δ μ v he,
      highInverse_apply_eigenvector B hB δ (-μ) (Z v) hz,map_smul,cutoffInverseValue_neg]
    simp
  ext x
  exact congrArg (fun L : E →ₗ[ℂ] E => L x) hlin

/-- A positive-grade source acquires negative grade after the odd inverse. -/
theorem highInverse_reverses_sign (B Z : E →L[ℂ] E) (hB : B.toLinearMap.IsSymmetric)
    (δ : ℝ) (hanti : ∀ x, Z (B x) = -B (Z x)) (b : E) (hb : Z b=b) :
    Z (highInverse B hB δ b) = -highInverse B hB δ b := by
  have h := congrArg (fun T : E →L[ℂ] E => T b) (highInverse_anticommutes B Z hB δ hanti)
  change Z (highInverse B hB δ b) = -highInverse B hB δ (Z b) at h
  rwa [hb] at h
end Operator

section Dilation
variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Computational Z on the Hermitian dilation's extra data bit. -/
def dilationSign : EuclideanSpace ℂ (D ⊕ D) →L[ℂ] EuclideanSpace ℂ (D ⊕ D) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (Sum.elim (fun i => x (.inl i)) (fun i => -x (.inr i)))
      map_add' := by intros; ext i; cases i <;> simp [add_comm]
      map_smul' := by intros; ext i; cases i <;> simp }

/-- The actual block matrix anticommutes with the actual extra-data-bit Z. -/
theorem dilationSign_anticommutes (B : Matrix D D ℂ) (x : EuclideanSpace ℂ (D ⊕ D)) :
    dilationSign (Matrix.toEuclideanCLM (n := D ⊕ D) (𝕜 := ℂ) (hermitianDilation B) x) =
      -Matrix.toEuclideanCLM (n := D ⊕ D) (𝕜 := ℂ) (hermitianDilation B) (dilationSign x) := by
  ext i
  cases i <;>
    simp [dilationSign,Matrix.ofLp_toEuclideanCLM,hermitianDilation,Matrix.mulVec,
      dotProduct,Fintype.sum_sum_type,Finset.sum_neg_distrib]

/-- Left-source support gives exact right support for the noisy truncated
inverse, regardless of its rank or the source's coordinates. -/
theorem highInverse_dilation_left_zero (B : Matrix D D ℂ) (δ : ℝ) (b : D → ℂ) (i : D) :
    highInverse (Matrix.toEuclideanCLM (n := D ⊕ D) (𝕜 := ℂ) (hermitianDilation B))
      (matrixHermitian_symmetric _ (hermitianDilation_hermitian B)) δ
      (WithLp.toLp 2 (Sum.elim b 0)) (.inl i) = 0 := by
  have hb : dilationSign (WithLp.toLp 2 (Sum.elim b 0))=WithLp.toLp 2 (Sum.elim b 0) := by
    ext j; cases j <;> simp [dilationSign]
  have h := highInverse_reverses_sign
    (Matrix.toEuclideanCLM (n := D ⊕ D) (𝕜 := ℂ) (hermitianDilation B)) dilationSign
    (matrixHermitian_symmetric _ (hermitianDilation_hermitian B)) δ
    (dilationSign_anticommutes B) _ hb
  have hi := congrArg (fun x : EuclideanSpace ℂ (D ⊕ D) => x (.inl i)) h
  let z := highInverse (Matrix.toEuclideanCLM (n := D ⊕ D) (𝕜 := ℂ) (hermitianDilation B))
    (matrixHermitian_symmetric _ (hermitianDilation_hermitian B)) δ
    (WithLp.toLp 2 (Sum.elim b 0))
  change z (.inl i) = -z (.inl i) at hi
  have htwo : (2:ℂ)*(highInverse
      (Matrix.toEuclideanCLM (n := D ⊕ D) (𝕜 := ℂ) (hermitianDilation B))
      (matrixHermitian_symmetric _ (hermitianDilation_hermitian B)) δ
      (WithLp.toLp 2 (Sum.elim b 0)) (.inl i)) = 0 := by linear_combination hi
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Normalization also has exact right support. -/
theorem normalized_highInverse_dilation_left_zero (B : Matrix D D ℂ) (δ : ℝ) (b : D → ℂ) (i : D) :
    NormedSpace.normalize
      (highInverse (Matrix.toEuclideanCLM (n := D ⊕ D) (𝕜 := ℂ) (hermitianDilation B))
        (matrixHermitian_symmetric _ (hermitianDilation_hermitian B)) δ
        (WithLp.toLp 2 (Sum.elim b 0))) (.inl i) = 0 := by
  simp only [NormedSpace.normalize,PiLp.smul_apply,highInverse_dilation_left_zero,smul_zero]
end Dilation

end OptimalQLS.PhysicalRobustness
