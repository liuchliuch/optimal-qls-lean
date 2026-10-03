import OptimalQLS.PolynomialTransform.PhysicalRegister
import OptimalQLS.PolynomialTransform.ElementaryCircuit

/-! # Projected phase macros on the full signal/data register -/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Matrix DirtyAncilla OptimalQLS.TransducerCompiler
variable {D : Type*} [Fintype D] [DecidableEq D]

def logicalPhase (a : ℕ) (branch : Bool) (z w : Circle) :
    Matrix.unitaryGroup (LogicalSignal a × D) ℂ :=
  diagonalPhase (fun x => logicalPhaseFunction a branch z w x.1)

/-- The elementary phase macro exactly intertwines the logical controlled phase. -/
theorem physicalPhase_intertwines (a : ℕ) (branch : Bool) (z w : Circle) :
    (elementaryPlacement (D := D) (phaseEval (physicalPhaseCode a branch z w))).val *
      basisInsertion (physicalClean a)=
    basisInsertion (physicalClean a)*(logicalPhase (D := D) a branch z w).val := by
  apply basisInsertion_intertwines
  intro x
  rw [logicalPhase,diagonalPhase_basis,Matrix.mulVec_smul,basisInsertion_basis]
  exact placeHom_basis_smul (Equiv.refl _) (phaseEval (physicalPhaseCode a branch z w))
    (physicalCleanSignal a x.1) (physicalCleanSignal a x.1) x.2
    (logicalPhaseFunction a branch z w x.1 : ℂ) (physicalPhaseCode_basis a branch z w x.1)

/-- Uniform, explicit linear-size synthesis of a logical controlled projected phase. -/
theorem logicalPhase_synthesis (a : ℕ) (branch : Bool) (z w : Circle) :
    ∃ code : List (PhaseGate (QSVTWire a)), code.length ≤ 781*(a+1) ∧
      (elementaryPlacement (D := D) (phaseEval code)).val*basisInsertion (physicalClean a)=
        basisInsertion (physicalClean a)*(logicalPhase (D := D) a branch z w).val :=
  ⟨physicalPhaseCode a branch z w,physicalPhaseCode_length a branch z w,
    physicalPhase_intertwines a branch z w⟩

end OptimalQLS.PolynomialTransform
