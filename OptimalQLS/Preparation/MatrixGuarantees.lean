import OptimalQLS.Preparation.IdealGeometry
import OptimalQLS.Preparation.Encoded

set_option maxHeartbeats 1600000
noncomputable section
namespace OptimalQLS.Preparation
open Matrix
variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The actual matrix-defined output and catalyst satisfy all of Lemma4.7,
with the preparation oracle's whole matrix retained. -/
theorem ideal_matrix_guarantees (H : Matrix D D ℂ) (Ub : Matrix.unitaryGroup D ℂ)
    (i₀ : D) (e : EuclideanSpace ℂ D) (he : ‖e‖=1) (hcol : ∀ i, Ub i i₀=e i)
    {κ s ŝ : ℝ} (hκ : 2≤κ) (hs : 1≤s) (hsκ : s≤κ)
    (hshlo : 3*s/8≤ŝ) (hshhi : ŝ≤5*s/2)
    (hprojlo : s^2/(2*κ^2) ≤
      ‖(LinearMap.ker (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H).toLinearMap).starProjection e‖^2)
    (hprojhi : ‖(LinearMap.ker (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H).toLinearMap).starProjection e‖^2≤s^2/κ^2)
    (hhalf : ‖(LinearMap.ker (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H).toLinearMap).starProjection e‖^2≤1/2) :
    let K := LinearMap.ker (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H).toLinearMap
    let U := idealUnitary H (preparedReflection Ub i₀)
    let r := overlapMixingParameter κ ŝ
    let q := WithLp.toLp 2 (fractionalCatalyst U r (WithLp.ofLp e))
    let ψ := WithLp.toLp 2 (fractionalAction U r*ᵥWithLp.ofLp e)
    (-1<r ∧ r<1 ∧ ‖ψ‖=1 ∧
      (inner ℂ (NormedSpace.normalize (K.starProjection e)) ψ).im=0 ∧
      1/30<(inner ℂ (NormedSpace.normalize (K.starProjection e)) ψ).re ∧
      q ∈ Submodule.span ℝ ({K.starProjection e,e-K.starProjection e} : Set (EuclideanSpace ℂ D)) ∧
      ‖q‖^2≤κ/(8*ŝ) ∧ κ/(8*ŝ)≤κ/(3*s)) := by
  let K := LinearMap.ker (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H).toLinearMap
  let U := idealUnitary H (preparedReflection Ub i₀)
  let r := overlapMixingParameter κ ŝ
  have hr : |r|<1 := abs_lt.mpr (overlapMixingParameter_mem (by linarith) (by nlinarith))
  have hu : unitaryOperator U=kernelMixingUnitary K e he := idealUnitary_operator_eq H Ub i₀ e he hcol
  have hqeq := fractionalCatalyst_to_operator U hr e
  rw [hu] at hqeq
  have hψeq : WithLp.toLp 2 (fractionalAction U r*ᵥWithLp.ofLp e) =
      operatorFractionalAction (kernelMixingUnitary K e he) r e := by
    change Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (fractionalAction U r) e = _
    rw [fractionalAction_to_operator U hr,hu]
  have h := lemma47 K e he hκ hs hsκ hshlo hshhi hprojlo hprojhi hhalf
  dsimp only at h ⊢
  dsimp only [r] at hqeq hψeq
  rw [← hqeq, ← hψeq] at h
  exact h

/-- Canonical Moore–Penrose inverses kill the exact kernel component. -/
theorem matrixPseudoInverse_kills_projection (H : Matrix D D ℂ) (hH : star H=H)
    (e : EuclideanSpace ℂ D) :
    Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (matrixPseudoInverse H hH)
      ((LinearMap.ker (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H).toLinearMap).starProjection e)=0 := by
  rw [matrixPseudoInverse,StarAlgEquiv.apply_symm_apply]
  have h := hermitianPseudoInverse_mul_kernel (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H)
    (matrixHermitian_symmetric H hH)
  have hh := congrArg (fun T : EuclideanSpace ℂ D →L[ℂ] EuclideanSpace ℂ D => T e) h
  simpa using hh

end OptimalQLS.Preparation
