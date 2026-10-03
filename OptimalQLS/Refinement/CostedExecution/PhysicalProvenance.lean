import OptimalQLS.Refinement.CostedExecution.Attachment
import OptimalQLS.Refinement.CostedExecution.Provenance
import OptimalQLS.Refinement.CostedExecution.Locality

/-! Same-coordinate gate locality and exact query provenance throughout the
actual repeated primitive execution, not just its source circuit. -/
noncomputable section
open scoped Classical
namespace OptimalQLS.Refinement.CostedExecution
open Matrix LowerBounds PolynomialTransform Preparation PhysicalPadding TransducerCompiler BinaryClock
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 16384
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {a n : ℕ} {κ s ŝ ε : ℝ} {h : BudgetParameters κ s ŝ}

def ReadsOneBit {A Aux Data : Type*} {w : ℕ} (E : State Aux Data ≃ Fin w)
    (p : QueryPort A (Fin w)) : Prop :=
  ∃ wire : Wire Aux Data, ∀ i k, p.control k=E.symm (p.wiring (i,k)) wire

def MatrixSource (I : PhysicalProgram.Implementation a n (ε:=ε) h)
    (p : QueryPort (Bits a × Bits n)
      (Fin (Fintype.card (PhysicalProgram.Register a n (preparationExponent κ))))) (adj : Bool) : Prop :=
  ∃ original : QueryPort (Bits a × Bits n) (PhysicalProgram.Register a n (preparationExponent κ)),
    NamedInstruction.matrixCall original adj∈I.circuit ∧
      p=Repetition.reindexPort (Fintype.equivFin _) original

def VectorSource (I : PhysicalProgram.Implementation a n (ε:=ε) h)
    (p : QueryPort (Bits n)
      (Fin (Fintype.card (PhysicalProgram.Register a n (preparationExponent κ))))) (adj : Bool) : Prop :=
  ∃ original : QueryPort (Bits n) (PhysicalProgram.Register a n (preparationExponent κ)),
    NamedInstruction.vectorCall original adj∈I.circuit ∧
      p=Repetition.reindexPort (Fintype.equivFin _) original

/-- Every named gate is a proved physical ≤2-qubit tensor. Every matrix/vector
query uses a port and adjoint direction occurring in the original circuit,
and its actual control reads a single bit in the measurement/reset layout. -/
def PhysicalSafety (I : PhysicalProgram.Implementation a n (ε:=ε) h)
    (p : Program (PhysicalProgram.Gate a n (preparationExponent κ)) (Bits a × Bits n) (Bits n)
      (PhysicalMeasurement.AuxWire a (preparationExponent κ)) (Fin n)
      (Fintype.card (PhysicalProgram.Register a n (preparationExponent κ)))) : Prop :=
  p.Allowed
    (fun g=>IsTwoLocal (PhysicalMeasurement.finiteRegisterCoordinates a n (preparationExponent κ)).symm
      (physicalGate I g))
    (fun p adj=>MatrixSource I p adj ∧
      ReadsOneBit (PhysicalMeasurement.finiteRegisterCoordinates a n (preparationExponent κ)) p)
    (fun p adj=>VectorSource I p adj ∧
      ReadsOneBit (PhysicalMeasurement.finiteRegisterCoordinates a n (preparationExponent κ)) p)

/-- Primitive provenance is preserved for every retry count and every branch. -/
theorem physicalSyntax_safe (I : PhysicalProgram.Implementation a n (ε:=ε) h) (R : ℕ) :
    PhysicalSafety I (physicalSyntax I R) := by
  unfold PhysicalSafety physicalSyntax
  apply allowed_repeated
  intro i hi
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  cases j with
  | gate g => exact physical_gate_finite_local a n _ (CompilerAttachment.preparationExponent_pos h) g
  | matrixCall p adj =>
    obtain ⟨f,hf⟩ := Implementation.matrixCall_reads_coordinate I p adj hj
    exact ⟨⟨p,hj,rfl⟩,controlWire a n _ f,hf⟩
  | vectorCall p adj =>
    exact ⟨⟨p,hj,rfl⟩,controlWire a n _ .preparation,
      Implementation.vectorCall_reads_coordinate I p adj hj⟩

end OptimalQLS.Refinement.CostedExecution
