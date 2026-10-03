import OptimalQLS.Perturbation.RobustPromises
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! # Exact matrix specialization of Lemma 7.1

The matrix norm here is explicitly the induced Euclidean operator norm.
The matrix/continuous-linear-map correspondence is a norm-preserving star
algebra equivalence, not an unproved correspondence between unrelated models.
-/

noncomputable section
namespace OptimalQLS.Perturbation
open scoped Matrix.Norms.L2Operator
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem toEuclideanCLM_inverse (A : Matrix n n ℂ) (hA : IsUnit A) :
    Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (Ring.inverse A) =
      Ring.inverse (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) := by
  have hleft : Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (Ring.inverse A) * Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A = 1 := by
    rw [← map_mul, Ring.inverse_mul_cancel A hA, map_one]
  have hright := Ring.mul_inverse_cancel (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A)
    (hA.map (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).toMonoidHom)
  exact left_inv_eq_right_inv hleft hright

/-- **Lemma 7.1** on actual finite complex matrices, with L2 norms and all
three estimates exactly as stated in the paper. -/
theorem lemma71_matrix (A B : Matrix n n ℂ) (hA : IsUnit A)
    (b : EuclideanSpace ℂ n) (hb : b ≠ 0) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hpert : ‖Ring.inverse A‖ * ‖B - A‖ ≤ ρ) :
    IsUnit B ∧
    ‖Ring.inverse B‖ ≤ ‖Ring.inverse A‖ / (1 - ρ) ∧
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (Ring.inverse A) b‖ / (1 + ρ) ≤
      ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (Ring.inverse B) b‖ ∧
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (Ring.inverse B) b‖ ≤
      ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (Ring.inverse A) b‖ / (1 - ρ) ∧
    ‖NormedSpace.normalize (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (Ring.inverse B) b) -
      NormedSpace.normalize (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (Ring.inverse A) b)‖ ≤ 2 * ρ := by
  let φ := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
  have hφA : IsUnit (φ A) := hA.map φ.toMonoidHom
  have hpert' : ‖Ring.inverse (φ A)‖ * ‖φ B - φ A‖ ≤ ρ := by
    rw [← toEuclideanCLM_inverse A hA, ← map_sub]
    simpa only [Matrix.l2_opNorm_toEuclideanCLM] using hpert
  have hp := lemma71 (φ A) (φ B) hφA b hb hρ0 hρ1 hpert'
  have hB : IsUnit B := by
    have h := hp.1.map φ.symm.toMonoidHom
    change IsUnit (φ.symm (φ B)) at h
    simpa using h
  refine ⟨hB, ?_⟩
  have hp' := hp.2
  rw [← toEuclideanCLM_inverse A hA, ← toEuclideanCLM_inverse B hB] at hp'
  simpa only [Matrix.l2_opNorm_toEuclideanCLM] using hp'

end OptimalQLS.Perturbation
