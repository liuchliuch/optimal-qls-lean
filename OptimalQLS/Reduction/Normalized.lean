import OptimalQLS.LowerBounds.HermitianDilation
import OptimalQLS.LowerBounds.StatePreparation
import OptimalQLS.LowerBounds.SumBlockEncoding
import OptimalQLS.Problem

/-! The active-space normalization and Hermitian reduction in Proposition 2.3.
The supplied oracles remain arbitrary full unitaries. No inverse is taken on
a zero-padded physical register. -/
noncomputable section
open scoped Matrix.Norms.L2Operator
namespace OptimalQLS.Reduction
open Matrix LowerBounds
variable {D S : Type*} [Fintype D] [DecidableEq D]
  [Fintype S] [DecidableEq S]

def normalizedMatrix (α : ℝ) (A : Matrix D D ℂ) : Matrix (D ⊕ D) (D ⊕ D) ℂ :=
  hermitianDilation (α⁻¹ • A)

def source (b : D → ℂ) : D ⊕ D → ℂ := Sum.elim b 0

def rightState (x : D → ℂ) : D ⊕ D → ℂ := Sum.elim 0 x

def preparation (Ub : Matrix.unitaryGroup D ℂ) : Matrix.unitaryGroup (D ⊕ D) ℂ :=
  blockSumUnitary Ub Ub

theorem preparation_columns (Ub : Matrix.unitaryGroup D ℂ) (i j : D) :
    preparation Ub (.inl i) (.inl j) = Ub i j ∧
    preparation Ub (.inr i) (.inr j) = Ub i j ∧
    preparation Ub (.inl i) (.inr j) = 0 ∧
    preparation Ub (.inr i) (.inl j) = 0 := by
  simp [preparation, blockSumUnitary]

theorem preparation_prepares (Ub : Matrix.unitaryGroup D ℂ) (zero : D)
    (b : D → ℂ) (h : ∀ i, Ub i zero = b i) :
    ∀ i, preparation Ub i (.inl zero) = source b i := by
  intro i
  cases i <;> simp [preparation, blockSumUnitary, source, h]

theorem source_norm (b : D → ℂ) : ‖WithLp.toLp 2 (source b)‖ = ‖WithLp.toLp 2 b‖ :=
  sumElim_norm_left b

theorem normalizedMatrix_hermitian (α : ℝ) (A : Matrix D D ℂ) :
    (normalizedMatrix α A).IsHermitian := hermitianDilation_hermitian _

theorem normalizedMatrix_inverse_relations {α : ℝ} (hα : 0 < α)
    (A : Matrix D D ℂ) (hA : IsUnit A) :
    (α • A⁻¹) * (α⁻¹ • A) = 1 ∧ (α⁻¹ • A) * (α • A⁻¹) = 1 := by
  have hdet := (Matrix.isUnit_iff_isUnit_det A).mp hA
  constructor <;>
    simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hα.ne',
      Matrix.nonsing_inv_mul A hdet, Matrix.mul_nonsing_inv A hdet]

theorem normalizedMatrix_inverse {α : ℝ} (hα : 0 < α)
    (A : Matrix D D ℂ) (hA : IsUnit A) :
    (normalizedMatrix α A)⁻¹ = hermitianInverseCandidate (α • A⁻¹) := by
  obtain ⟨hl,hr⟩ := normalizedMatrix_inverse_relations hα A hA
  exact hermitianDilation_inverse _ _ hl hr

theorem normalizedMatrix_isUnit {α : ℝ} (hα : 0 < α)
    (A : Matrix D D ℂ) (hA : IsUnit A) : IsUnit (normalizedMatrix α A) := by
  obtain ⟨hl,hr⟩ := normalizedMatrix_inverse_relations hα A hA
  apply isUnit_iff_exists_inv'.mpr
  exact ⟨hermitianInverseCandidate (α • A⁻¹), hermitianInverseCandidate_mul _ _ hl hr⟩

theorem normalizedMatrix_norm {α : ℝ} (hα : 0 < α) (A : Matrix D D ℂ) :
    ‖normalizedMatrix α A‖ = α⁻¹ * ‖A‖ := by
  rw [normalizedMatrix, hermitianDilation_norm, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hα)]

theorem normalizedMatrix_inverse_norm {α : ℝ} (hα : 0 < α)
    (A : Matrix D D ℂ) (hA : IsUnit A) :
    ‖(normalizedMatrix α A)⁻¹‖ = α * ‖A⁻¹‖ := by
  rw [normalizedMatrix_inverse hα A hA, hermitianInverseCandidate_norm,
    norm_smul, Real.norm_eq_abs, abs_of_pos hα]

theorem normalizedMatrix_inverse_source {α : ℝ} (hα : 0 < α)
    (A : Matrix D D ℂ) (hA : IsUnit A) (b : D → ℂ) :
    (normalizedMatrix α A)⁻¹ *ᵥ source b = rightState (α • (A⁻¹ *ᵥ b)) := by
  obtain ⟨hl,hr⟩ := normalizedMatrix_inverse_relations hα A hA
  simpa [normalizedMatrix, source, rightState, Matrix.smul_mulVec] using
    hermitianDilation_inverse_source (α⁻¹ • A) (α • A⁻¹) hl hr b

theorem normalized_solution_scale {α : ℝ} (hα : 0 < α)
    (A : Matrix D D ℂ) (hA : IsUnit A) (b : D → ℂ) :
    ‖WithLp.toLp 2 ((normalizedMatrix α A)⁻¹ *ᵥ source b)‖ =
      α * ‖WithLp.toLp 2 (A⁻¹ *ᵥ b)‖ := by
  rw [normalizedMatrix_inverse_source hα A hA, rightState, sumElim_norm_right]
  change ‖α • WithLp.toLp 2 (A⁻¹ *ᵥ b)‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hα]

theorem normalized_solution_direction {α : ℝ} (hα : 0 < α)
    (A : Matrix D D ℂ) (hA : IsUnit A) (b : D → ℂ) :
    NormedSpace.normalize (WithLp.toLp 2 ((normalizedMatrix α A)⁻¹ *ᵥ source b)) =
      WithLp.toLp 2 (rightState (fun i =>
        (NormedSpace.normalize (WithLp.toLp 2 (A⁻¹ *ᵥ b)) : EuclideanSpace ℂ D) i)) := by
  rw [normalizedMatrix_inverse_source hα A hA]
  have hsmul : WithLp.toLp 2 (rightState (α • (A⁻¹ *ᵥ b))) =
      α • WithLp.toLp 2 (rightState (A⁻¹ *ᵥ b)) := by
    ext i; cases i <;> simp [rightState]
  rw [hsmul, NormedSpace.normalize_smul_of_pos hα]
  simp only [NormedSpace.normalize, rightState, sumElim_norm_right]
  ext i; cases i <;> simp

theorem inverse_source_nonzero (A : Matrix D D ℂ) (hA : IsUnit A)
    (b : D → ℂ) (hb : ‖WithLp.toLp 2 b‖ = 1) : WithLp.toLp 2 (A⁻¹ *ᵥ b) ≠ 0 := by
  intro hzero
  have hz : A⁻¹ *ᵥ b = 0 := congrArg WithLp.ofLp hzero
  have hback : A *ᵥ (A⁻¹ *ᵥ b) = b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A
      ((Matrix.isUnit_iff_isUnit_det A).mp hA), Matrix.one_mulVec]
  rw [hz, Matrix.mulVec_zero] at hback
  rw [← hback, WithLp.toLp_zero, norm_zero] at hb
  norm_num at hb

theorem normalized_original_solution_unit (A : Matrix D D ℂ) (hA : IsUnit A)
    (b : D → ℂ) (hb : ‖WithLp.toLp 2 b‖ = 1) :
    ‖NormedSpace.normalize (WithLp.toLp 2 (A⁻¹ *ᵥ b))‖ = 1 :=
  NormedSpace.norm_normalize (inverse_source_nonzero A hA b hb)

theorem normalized_encoding [Nonempty D] (s : S) {α : ℝ}
    (A : Matrix D D ℂ) (UA : Matrix.unitaryGroup (S × D) ℂ)
    (henc : IsBlockEncoding s α 0 UA A) :
    IsBlockEncoding s 1 0 (dilationEncoding UA) (normalizedMatrix α A) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [dilationEncoding_signalBlock, normalizedMatrix, exact_block_eq henc,
    smul_smul, inv_mul_cancel₀ henc.1.ne', one_smul, one_smul]
  simp

theorem normalized_bounds [Nonempty D] (s : S) {α κ : ℝ}
    (A : Matrix D D ℂ) (UA : Matrix.unitaryGroup (S × D) ℂ)
    (henc : IsBlockEncoding s α 0 UA A) (hA : IsUnit A)
    (hinv : α * ‖A⁻¹‖ ≤ κ) :
    ‖normalizedMatrix α A‖ ≤ 1 ∧ ‖(normalizedMatrix α A)⁻¹‖ ≤ κ := by
  constructor
  · rw [normalizedMatrix_norm henc.1]
    calc α⁻¹ * ‖A‖ ≤ α⁻¹ * α :=
      mul_le_mul_of_nonneg_left (norm_le_of_exact_block henc) (inv_nonneg.mpr henc.1.le)
    _ = 1 := inv_mul_cancel₀ henc.1.ne'
  · rwa [normalizedMatrix_inverse_norm henc.1 A hA]

theorem relaxed_estimate_transport {α estimate : ℝ} (hα : 0 < α)
    (A : Matrix D D ℂ) (hA : IsUnit A) (b : D → ℂ)
    (hl : 3 * (α * ‖WithLp.toLp 2 (A⁻¹ *ᵥ b)‖) / 8 ≤ estimate)
    (hu : estimate ≤ 5 * (α * ‖WithLp.toLp 2 (A⁻¹ *ᵥ b)‖) / 2) :
    3 * ‖WithLp.toLp 2 ((normalizedMatrix α A)⁻¹ *ᵥ source b)‖ / 8 ≤ estimate ∧
    estimate ≤ 5 * ‖WithLp.toLp 2 ((normalizedMatrix α A)⁻¹ *ᵥ source b)‖ / 2 := by
  rw [normalized_solution_scale hα A hA]
  exact ⟨hl,hu⟩

theorem factor_two_estimate_transport {α estimate : ℝ} (hα : 0 < α)
    (A : Matrix D D ℂ) (hA : IsUnit A) (b : D → ℂ)
    (hl : (α * ‖WithLp.toLp 2 (A⁻¹ *ᵥ b)‖) / 2 ≤ estimate)
    (hu : estimate ≤ 2 * (α * ‖WithLp.toLp 2 (A⁻¹ *ᵥ b)‖)) :
    ‖WithLp.toLp 2 ((normalizedMatrix α A)⁻¹ *ᵥ source b)‖ / 2 ≤ estimate ∧
    estimate ≤ 2 * ‖WithLp.toLp 2 ((normalizedMatrix α A)⁻¹ *ᵥ source b)‖ := by
  rw [normalized_solution_scale hα A hA]
  exact ⟨hl,hu⟩

end OptimalQLS.Reduction
