import OptimalQLS.Reduction.Normalized
import OptimalQLS.PhysicalPadding.Dilation

/-! Normalization commutes with physical padding. Inverse statements use the
active inverse, and never demand invertibility of the zero-padded matrix. -/
noncomputable section
open scoped Matrix.Norms.L2Operator
namespace OptimalQLS.Reduction
open Matrix LowerBounds PhysicalPadding
variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

theorem physical_normalization_commutes (f : D ↪ P) (α : ℝ) (A : Matrix D D ℂ) :
    zeroExtend (sumIndex f) (normalizedMatrix α A) =
      normalizedMatrix α (zeroExtend f A) := by
  simp only [normalizedMatrix, zeroExtend_hermitianDilation, zeroExtend_real_smul]

theorem physical_source (f : D ↪ P) (b : EuclideanSpace ℂ D) :
    coordinateIsometry (sumIndex f) (WithLp.toLp 2 (source (fun i => b i))) =
      WithLp.toLp 2 (source (fun i => coordinateIsometry f b i)) :=
  sumIndex_source_left f b

theorem activeInverse_dilation_source (f : D ↪ P) {α : ℝ} (hα : 0 < α)
    (A : Matrix D D ℂ) (hA : IsUnit A) (b : D → ℂ) :
    Matrix.toEuclideanCLM (n := P ⊕ P) (𝕜 := ℂ)
      (activeInverse (sumIndex f) (normalizedMatrix α A))
      (coordinateIsometry (sumIndex f) (WithLp.toLp 2 (source b))) =
      coordinateIsometry (sumIndex f)
        (WithLp.toLp 2 (rightState (α • (A⁻¹ *ᵥ b)))) := by
  rw [activeInverse_apply, ← Matrix.nonsing_inv_eq_ringInverse]
  change coordinateIsometry (sumIndex f)
    (WithLp.toLp 2 ((normalizedMatrix α A)⁻¹ *ᵥ source b)) = _
  rw [normalizedMatrix_inverse_source hα A hA]

theorem activeInverse_dilation_scale (f : D ↪ P) {α : ℝ} (hα : 0 < α)
    (A : Matrix D D ℂ) (hA : IsUnit A) (b : D → ℂ) :
    ‖Matrix.toEuclideanCLM (n := P ⊕ P) (𝕜 := ℂ)
      (activeInverse (sumIndex f) (normalizedMatrix α A))
      (coordinateIsometry (sumIndex f) (WithLp.toLp 2 (source b)))‖ =
      α * ‖WithLp.toLp 2 (A⁻¹ *ᵥ b)‖ := by
  rw [activeInverse_apply, (coordinateIsometry (sumIndex f)).norm_map,
    ← Matrix.nonsing_inv_eq_ringInverse]
  exact normalized_solution_scale hα A hA b

end OptimalQLS.Reduction
