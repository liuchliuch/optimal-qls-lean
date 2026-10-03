import OptimalQLS.Preparation.Ideal
import OptimalQLS.Preparation.PlaneCosts

noncomputable section
namespace OptimalQLS.Preparation
open Matrix
variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Rank-one matrix/continuous-operator correspondence with the actual complex inner product. -/
theorem outerProduct_mulVec (e v : EuclideanSpace ℂ D) (i : D) :
    ((Matrix.of (fun j k => e j * star (e k))) *ᵥ WithLp.ofLp v) i =
      inner ℂ e v * e i := by
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, PiLp.inner_apply,
    RCLike.inner_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  change e i * star (e j) * v j = v j * star (e j) * e i
  ring

theorem preparedReflection_to_operator (Ub : Matrix.unitaryGroup D ℂ) (i₀ : D)
    (e : EuclideanSpace ℂ D) (he : ‖e‖=1) (hcol : ∀ i, Ub i i₀=e i) :
    Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (preparedReflection Ub i₀ : Matrix D D ℂ) =
      (vectorReflectionUnitary e he : EuclideanSpace ℂ D →L[ℂ] EuclideanSpace ℂ D) := by
  apply ContinuousLinearMap.ext
  intro v
  ext i
  rw [preparedReflection_matrix]
  change (((2:ℂ) • Matrix.of (fun j k => Ub j i₀ * star (Ub k i₀))-1)*ᵥWithLp.ofLp v) i = _
  simp_rw [hcol]
  rw [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec]
  change (2:ℂ) * ((Matrix.of (fun j k => e j * star (e k)))*ᵥWithLp.ofLp v) i - v i = _
  rw [outerProduct_mulVec,vectorReflectionUnitary_apply]
  simp [smul_smul,mul_assoc]

theorem kernelReflectionMatrix_to_operator (H : Matrix D D ℂ) :
    Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (kernelReflectionMatrix H : Matrix D D ℂ) =
      (projectionReflectionUnitary
        (LinearMap.ker (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H).toLinearMap).starProjection
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
          (LinearMap.ker (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H).toLinearMap).starProjection_isSymmetric)
        (LinearMap.ker (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H).toLinearMap).isIdempotentElem_starProjection :
        EuclideanSpace ℂ D →L[ℂ] EuclideanSpace ℂ D) := by
  let φ := Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)
  change φ ((2:ℝ) • matrixKernelProjection H-1) =
    (2:ℝ) • (LinearMap.ker (φ H).toLinearMap).starProjection-1
  rw [two_smul,map_sub,map_add,map_one]
  change φ (φ.symm (LinearMap.ker (φ H).toLinearMap).starProjection)+
    φ (φ.symm (LinearMap.ker (φ H).toLinearMap).starProjection)-1 = _
  rw [φ.apply_symm_apply]
  module

/-- Matrix and Hilbert-space definitions use exactly the same two-reflection action. -/
theorem idealUnitary_to_operator (H : Matrix D D ℂ) (Ub : Matrix.unitaryGroup D ℂ)
    (i₀ : D) (e : EuclideanSpace ℂ D) (he : ‖e‖=1) (hcol : ∀ i, Ub i i₀=e i) :
    Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (idealUnitary H (preparedReflection Ub i₀) : Matrix D D ℂ) =
      (kernelMixingUnitary (LinearMap.ker (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H).toLinearMap) e he :
        EuclideanSpace ℂ D →L[ℂ] EuclideanSpace ℂ D) := by
  change Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)
    (-((preparedReflection Ub i₀ : Matrix D D ℂ)*(kernelReflectionMatrix H : Matrix D D ℂ))) = _
  rw [map_neg,map_mul,preparedReflection_to_operator Ub i₀ e he hcol,kernelReflectionMatrix_to_operator]
  rfl

/-- The actual star-algebra equivalence preserves real scalar coefficients. -/
theorem matrix_to_operator_real_smul (r : ℝ) (M : Matrix D D ℂ) :
    Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (r • M) =
      r • Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) M :=
  (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toLinearMap.map_smul_of_tower r M

/-- The exact image of a matrix unitary under the norm-preserving star algebra equivalence. -/
def unitaryOperator (U : Matrix.unitaryGroup D ℂ) :
    unitary (EuclideanSpace ℂ D →L[ℂ] EuclideanSpace ℂ D) :=
  ⟨Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) U,
    Unitary.map_mem (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)) U.property⟩

theorem idealUnitary_operator_eq (H : Matrix D D ℂ) (Ub : Matrix.unitaryGroup D ℂ)
    (i₀ : D) (e : EuclideanSpace ℂ D) (he : ‖e‖=1) (hcol : ∀ i, Ub i i₀=e i) :
    unitaryOperator (idealUnitary H (preparedReflection Ub i₀)) =
      kernelMixingUnitary (LinearMap.ker (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H).toLinearMap) e he := by
  apply Subtype.ext
  exact idealUnitary_to_operator H Ub i₀ e he hcol

theorem fractionalDenominator_to_operator (U : Matrix.unitaryGroup D ℂ) (r : ℝ) :
    Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (fractionalDenominator U r) =
      1-r • (unitaryOperator U : EuclideanSpace ℂ D →L[ℂ] EuclideanSpace ℂ D) := by
  rw [fractionalDenominator,map_sub,map_one,matrix_to_operator_real_smul]
  rfl

theorem fractionalCatalyst_to_operator (U : Matrix.unitaryGroup D ℂ) {r : ℝ} (hr : |r|<1)
    (e : EuclideanSpace ℂ D) :
    WithLp.toLp 2 (fractionalCatalyst U r (WithLp.ofLp e)) =
      operatorFractionalCatalyst (unitaryOperator U) r e := by
  change Real.sqrt (1-r^2) •
    (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (Ring.inverse (fractionalDenominator U r))) e =
    Real.sqrt (1-r^2) • Ring.inverse
      (1-r • (unitaryOperator U : EuclideanSpace ℂ D →L[ℂ] EuclideanSpace ℂ D)) e
  rw [Perturbation.toEuclideanCLM_inverse _ (fractionalDenominator_isUnit U hr),
    fractionalDenominator_to_operator]

theorem fractionalAction_to_operator (U : Matrix.unitaryGroup D ℂ) {r : ℝ} (hr : |r|<1) :
    Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (fractionalAction U r) =
      operatorFractionalAction (unitaryOperator U) r := by
  rw [fractionalAction,map_mul, fractionalNumerator,map_sub,matrix_to_operator_real_smul,map_one,
    Perturbation.toEuclideanCLM_inverse _ (fractionalDenominator_isUnit U hr),
    fractionalDenominator_to_operator]
  rfl

end OptimalQLS.Preparation
