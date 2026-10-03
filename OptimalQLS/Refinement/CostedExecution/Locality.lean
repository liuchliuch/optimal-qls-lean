import OptimalQLS.Refinement.PhysicalResources
import OptimalQLS.Refinement.CostedExecution.GateLocality

/-! # Common-coordinate locality for the actual physical execution

Every oracle control is a single literal coordinate in the very same bit
register used by the measurement and reset program. -/
noncomputable section
namespace OptimalQLS.Refinement.CostedExecution
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform
open PhysicalProgram PhysicalMeasurement
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

/-- The actual three control bits, in the measurement/reset coordinate system. -/
def controlWire (a n ℓ : ℕ) : PhysicalProgram.Flag → AuxWire a ℓ ⊕ Fin n
  | .preparation => .inl (.inr (.inl (.inr (.inr (.inl ())))))
  | .filter => .inl (.inr (.inr (.inl (.inr (PolynomialTransform.flagWire (a+4))))))
  | .correction => .inl (.inl (.inr (PolynomialTransform.flagWire a)))

/-- No predicate or extra control computation is hidden in the reindexing. -/
theorem flagValue_is_coordinate (a n ℓ : ℕ) (f : PhysicalProgram.Flag)
    (x : Register a n ℓ) :
    PhysicalProgram.flagValue a n ℓ f x =
      (registerCoordinates a n ℓ).symm x (controlWire a n ℓ f) := by
  cases f <;> rfl

/-- Query-port provenance survives the identical finite register reindexing
used by the operational program. -/
theorem reindexPort_reads_coordinate {A : Type*} [Fintype A] [DecidableEq A]
    (a n ℓ : ℕ) (p : QueryPort A (Register a n ℓ)) (f : PhysicalProgram.Flag)
    (hp : PhysicalProgram.ReadsFlag p (PhysicalProgram.flagValue a n ℓ f)) :
    ∀ i k, (Repetition.reindexPort (Fintype.equivFin _) p).control k =
      (finiteRegisterCoordinates a n ℓ).symm
        ((Repetition.reindexPort (Fintype.equivFin _) p).wiring (i,k))
          (controlWire a n ℓ f) := by
  intro i k
  change p.control k = (registerCoordinates a n ℓ).symm
    ((Fintype.equivFin (Register a n ℓ)).symm
      ((Fintype.equivFin (Register a n ℓ)) (p.wiring (i,k)))) _
  rw [Equiv.symm_apply_apply, ←flagValue_is_coordinate]
  exact hp i k

variable {a n : ℕ} {κ s ŝ ε : ℝ} {h : BudgetParameters κ s ŝ}

/-- Every actual matrix query in the selected circuit reads one displayed
physical qubit, even after lowering to the finite-register execution. -/
theorem Implementation.matrixCall_reads_coordinate
    (I : PhysicalProgram.Implementation a n (ε := ε) h)
    (p : QueryPort (Bits a × Bits n) (Register a n (preparationExponent κ)))
    (adj : Bool) (hp : NamedInstruction.matrixCall p adj ∈ I.circuit) :
    ∃ f : PhysicalProgram.Flag, ∀ i k,
      (Repetition.reindexPort (Fintype.equivFin _) p).control k =
        (finiteRegisterCoordinates a n (preparationExponent κ)).symm
          ((Repetition.reindexPort (Fintype.equivFin _) p).wiring (i,k))
            (controlWire a n (preparationExponent κ) f) := by
  obtain ⟨f,hf⟩ := I.singleControlled.1 p adj hp
  exact ⟨f,reindexPort_reads_coordinate _ _ _ p f hf⟩

/-- The original vector oracle uses the same preparation flag coordinate. -/
theorem Implementation.vectorCall_reads_coordinate
    (I : PhysicalProgram.Implementation a n (ε := ε) h)
    (p : QueryPort (Bits n) (Register a n (preparationExponent κ)))
    (adj : Bool) (hp : NamedInstruction.vectorCall p adj ∈ I.circuit) :
    ∀ i k, (Repetition.reindexPort (Fintype.equivFin _) p).control k =
      (finiteRegisterCoordinates a n (preparationExponent κ)).symm
        ((Repetition.reindexPort (Fintype.equivFin _) p).wiring (i,k))
          (controlWire a n (preparationExponent κ) .preparation) :=
  reindexPort_reads_coordinate _ _ _ p .preparation (I.singleControlled.2 p adj hp)

end OptimalQLS.Refinement.CostedExecution
