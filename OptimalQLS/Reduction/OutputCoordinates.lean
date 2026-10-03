import OptimalQLS.Reduction.PhysicalAdapter.Frames
import OptimalQLS.Refinement.PhysicalExecution
import OptimalQLS.Reduction.Physical

/-! # Literal head-bit dilation and output-extraction coordinates -/
noncomputable section
namespace OptimalQLS.Reduction
open Matrix PhysicalPadding TransducerCompiler BinaryClock Refinement.PhysicalExecution PolynomialTransform
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
variable {D P Q : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]
  [Fintype Q] [DecidableEq Q]

theorem coordinateIsometry_postEquiv (f : D ↪ P) (e : P ≃ Q) (v : EuclideanSpace ℂ D) :
    coordinateIsometry (f.trans e.toEmbedding) v=
      WithLp.toLp 2 ((WithLp.ofLp (coordinateIsometry f v)) ∘ e.symm) := by
  ext q
  have he (i : D) : q=e (f i) ↔ e.symm q=f i := by
    constructor
    · intro h; simpa using congrArg e.symm h
    · intro h; simpa using congrArg e h
  simp [coordinateIsometry_apply,insertion,basisInsertion,Matrix.mulVec,dotProduct,he]

theorem zeroExtend_postEquiv (f : D ↪ P) (e : P ≃ Q) (A : Matrix D D ℂ) :
    zeroExtend (f.trans e.toEmbedding) A=(zeroExtend f A).submatrix e.symm e.symm := by
  ext q r
  have he (q : Q) (i : D) : q=e (f i) ↔ e.symm q=f i := by
    constructor
    · intro h; simpa using congrArg e.symm h
    · intro h; simpa using congrArg e h
  simp [zeroExtend,insertion,basisInsertion,Matrix.mul_apply,Matrix.conjTranspose_apply,he]

def dilationActive {n : ℕ} (f : D ↪ Bits n) : (D ⊕ D) ↪ Bits (n+1) :=
  (sumIndex f).trans (PhysicalAdapter.sumBits n).symm.toEmbedding

def extractionCoordinates (n : ℕ) : (Fin (2^n) ⊕ Fin (2^n)) ≃ Fin (2^(n+1)) :=
  (Equiv.sumCongr (HadamardClock.bitsFinEquiv n).symm (HadamardClock.bitsFinEquiv n).symm).trans
    ((PhysicalAdapter.sumBits n).symm.trans (HadamardClock.bitsFinEquiv (n+1)))

theorem dilationActive_matrix {n : ℕ} (f : D ↪ Bits n) (α : ℝ) (A : Matrix D D ℂ) :
    zeroExtend (dilationActive f) (normalizedMatrix α A)=
      (normalizedMatrix α (zeroExtend f A)).submatrix (PhysicalAdapter.sumBits n) (PhysicalAdapter.sumBits n) := by
  rw [dilationActive,zeroExtend_postEquiv,physical_normalization_commutes]
  rfl

/-- The additional data bit has exact right support for a right-supported
logical vector, including all noncontiguous unused-coordinate padding. -/
theorem dilationActive_right_output {n : ℕ} (f : D ↪ Bits n) (v : EuclideanSpace ℂ D) :
    outputCoordinates (n+1) (coordinateIsometry (dilationActive f)
      (WithLp.toLp 2 (rightState (WithLp.ofLp v))))=
    WithLp.toLp 2 ((rightState (WithLp.ofLp (outputCoordinates n (coordinateIsometry f v)))) ∘
      (extractionCoordinates n).symm) := by
  have hs : coordinateIsometry (sumIndex f) (WithLp.toLp 2 (rightState (WithLp.ofLp v)))=
      WithLp.toLp 2 (rightState (WithLp.ofLp (coordinateIsometry f v))) := by
    simpa only [rightState] using sumIndex_source_right f v
  rw [dilationActive,coordinateIsometry_postEquiv,hs]
  ext i
  rw [outputCoordinates_apply]
  change (rightState (WithLp.ofLp (coordinateIsometry f v)))
      (PhysicalAdapter.sumBits n ((HadamardClock.bitsFinEquiv (n+1)).symm i))=_
  generalize hx : PhysicalAdapter.sumBits n ((HadamardClock.bitsFinEquiv (n+1)).symm i)=x
  cases x with
  | inl x => simp [extractionCoordinates,rightState,hx]
  | inr x => simp [extractionCoordinates,rightState,outputCoordinates_apply,hx]

theorem normalized_dilation_output {n : ℕ} (f : D ↪ Bits n) {α : ℝ} (hα : 0<α)
    (A : Matrix D D ℂ) (hA : IsUnit A) (b : D → ℂ) :
    outputCoordinates (n+1) (coordinateIsometry (dilationActive f)
      (NormedSpace.normalize (WithLp.toLp 2 ((normalizedMatrix α A)⁻¹*ᵥsource b))))=
    WithLp.toLp 2 ((rightState (WithLp.ofLp (outputCoordinates n (coordinateIsometry f
      (NormedSpace.normalize (WithLp.toLp 2 (A⁻¹*ᵥb))))))) ∘ (extractionCoordinates n).symm) := by
  rw [normalized_solution_direction hα A hA b]
  exact dilationActive_right_output f _

end OptimalQLS.Reduction
