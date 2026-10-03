import OptimalQLS.Refinement.CostedExecution.Complete
import OptimalQLS.Refinement.CostedExecution.QueryLocality

/-! Full control AND argument-register placement on the normalized physical tree. -/
noncomputable section
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
open scoped Classical
namespace OptimalQLS.Refinement.CostedExecution
open Matrix LowerBounds PolynomialTransform Preparation PhysicalPadding TransducerCompiler BinaryClock
variable {a n : ℕ} {κ s ŝ ε : ℝ} {h : BudgetParameters κ s ŝ}
attribute [local irreducible] repeated Program.lower Repetition.repeatProgram

def FullPhysicalSafety (I : PhysicalProgram.Implementation a n (ε := ε) h) (R : ℕ) : Prop :=
  (physicalSyntax I R).Allowed
    (fun g=>IsTwoLocal (PhysicalMeasurement.finiteRegisterCoordinates a n (preparationExponent κ)).symm
      (physicalGate I g))
    (fun p adj=>MatrixSource I p adj ∧ Nonempty (LiteralQueryPlacement (matrixArguments a n)
      (PhysicalMeasurement.finiteRegisterCoordinates a n (preparationExponent κ)).symm p))
    (fun p adj=>VectorSource I p adj ∧ Nonempty (LiteralQueryPlacement (Equiv.refl (Bits n))
      (PhysicalMeasurement.finiteRegisterCoordinates a n (preparationExponent κ)).symm p))

/-- The actual same primitive syntax has literal selected argument/control
wires and untouched spectators for every original oracle occurrence. -/
theorem physicalSyntax_full_safe (I : PhysicalProgram.Implementation a n (ε := ε) h) (R : ℕ) :
    FullPhysicalSafety I R := by
  unfold FullPhysicalSafety physicalSyntax
  apply allowed_repeated
  intro i hi
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  cases j with
  | gate g => exact physical_gate_finite_local a n _ (CompilerAttachment.preparationExponent_pos h) g
  | matrixCall p adj =>
    obtain ⟨L⟩ := Implementation.matrixCall_literal_placement I p adj hj
    exact ⟨⟨p,hj,rfl⟩,⟨L.reindex (Fintype.equivFin _)⟩⟩
  | vectorCall p adj =>
    obtain ⟨L⟩ := Implementation.vectorCall_literal_placement I p adj hj
    exact ⟨⟨p,hj,rfl⟩,⟨L.reindex (Fintype.equivFin _)⟩⟩


end OptimalQLS.Refinement.CostedExecution
