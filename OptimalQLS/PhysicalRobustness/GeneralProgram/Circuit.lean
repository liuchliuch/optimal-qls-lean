import OptimalQLS.PhysicalRobustness.GeneralProgram.Target
import OptimalQLS.Reduction.DirectMeasurement

/-! One original-oracle list, with the actual joint auxiliary/head acceptance. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open scoped Classical Matrix.Norms.L2Operator
namespace OptimalQLS.PhysicalRobustness.GeneralProgram
open Matrix LowerBounds PhysicalPadding Reduction TransducerCompiler BinaryClock PolynomialTransform
open Refinement Refinement.PhysicalExecution Refinement.Repetition
variable {a n : ℕ} {κ ŝ ε : ℝ}

abbrev Implementation (a n : ℕ) (κ ŝ ε : ℝ) :=
  PhysicalRobustness.PhysicalProgram.Implementation a (n+1) κ ŝ ε

def circuit (I : Implementation a n κ ŝ ε) :=
  PhysicalAdapter.substitute a n (preparationExponent (2*κ)) I.circuit

def runCircuit (I : Implementation a n κ ŝ ε) :=
  (circuit I).toQuery (PhysicalAdapter.gateEval a n _
    (Preparation.CompilerAttachment.preparationExponent_pos I.budget))

theorem allowed (I : Implementation a n κ ŝ ε) : PhysicalAdapter.Allowed I.circuit := by
  constructor
  · exact Refinement.PhysicalProgram.program_matrix_ports a (n+1) _ I.preparation I.preparation_strict
      I.filter I.filter_ports I.correction I.correction_ports
  · exact Refinement.PhysicalProgram.program_vector_ports a (n+1) _ I.preparation I.preparation_strict
      I.filter I.filter_vector I.correction I.correction_vector

theorem circuit_safe (I : Implementation a n κ ŝ ε) : PhysicalAdapter.Safe (circuit I) :=
  PhysicalAdapter.substitute_safe a n _ (Preparation.CompilerAttachment.preparationExponent_pos I.budget) I.circuit

theorem circuit_counts (I : Implementation a n κ ŝ ε) :
    (runCircuit I).matrixQueries=2*I.runCircuit.matrixQueries ∧
    (runCircuit I).vectorQueries=I.runCircuit.vectorQueries ∧
    (circuit I).workGates≤I.circuit.workGates+4801*I.runCircuit.matrixQueries :=
  PhysicalAdapter.substitute_counts a n _ (Preparation.CompilerAttachment.preparationExponent_pos I.budget) I.circuit

def fullAccepted (I : Implementation a n κ ŝ ε)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :=
  acceptedVector (runCircuit I) (AdaptedExecution.acceptance a n (preparationExponent (2*κ)))
    (AdaptedExecution.initial a n (preparationExponent (2*κ))) UA Ub

def accepted (I : Implementation a n κ ŝ ε)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :=
  acceptedVector (runCircuit I) (DirectExecution.acceptance a n (preparationExponent (2*κ)))
    (AdaptedExecution.initial a n (preparationExponent (2*κ))) UA Ub

theorem fullAccepted_exact (I : Implementation a n κ ŝ ε)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    fullAccepted I UA Ub=outputCoordinates (n+1)
      (I.accepted (PhysicalAdapter.matrixOracle UA) (PhysicalAdapter.vectorOracle Ub)) := by
  calc
    _=acceptedVector I.runCircuit (dataEmbedding a (n+1) (preparationExponent (2*κ)))
        (Refinement.PhysicalProgram.initial a (n+1) (preparationExponent (2*κ)))
        (PhysicalAdapter.matrixOracle UA) (PhysicalAdapter.vectorOracle Ub) :=
      clean_circuit_accepted (AdaptedExecution.cleanEmbedding a n _) _ (runCircuit I) UA Ub _
        (PhysicalAdapter.substitute_intertwines a n _ _ I.circuit (allowed I) UA Ub) _
    _=_ := I.accepted_coordinates _ _

theorem accepted_right (I : Implementation a n κ ŝ ε)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    accepted I UA Ub=rightPart (sumOutput n
      (I.accepted (PhysicalAdapter.matrixOracle UA) (PhysicalAdapter.vectorOracle Ub))) := by
  have he : accepted I UA Ub=rightPart (coordinateIsometry (extractionCoordinates n).symm.toEmbedding
      (fullAccepted I UA Ub)) := by
    ext i
    change _=coordinateIsometry (extractionCoordinates n).symm.toEmbedding (fullAccepted I UA Ub) (.inr i)
    rw [DirectExecution.coordinate_equiv_apply]
    rfl
  rw [he,fullAccepted_exact]
  rfl

def execution (I : Implementation a n κ ŝ ε) :=
  repeatProgram (finiteRun (runCircuit I))
    (finiteAccept (DirectExecution.acceptance a n (preparationExponent (2*κ))))
    (AdaptedExecution.initialIndex a n (preparationExponent (2*κ))) (0 : Fin (2^n)) 600000

/-- Joint acceptance uses exactly the shared layout's physical single-bit pattern. -/
theorem execution_eq_physical (I : Implementation a n κ ŝ ε) :
    execution I=repeatProgram (finiteRun (runCircuit I))
      (Repetition.reindexEmbedding (DirectMeasurement.finiteCoordinates a n (preparationExponent (2*κ)))
        (HadamardClock.bitsFinEquiv n)
        (Repetition.Physical.auxEmbedding (DirectMeasurement.acceptancePattern a (preparationExponent (2*κ)))))
      (AdaptedExecution.initialIndex a n (preparationExponent (2*κ))) (0 : Fin (2^n)) 600000 := by
  unfold execution
  rw [DirectMeasurement.acceptance_exact]

end OptimalQLS.PhysicalRobustness.GeneralProgram
