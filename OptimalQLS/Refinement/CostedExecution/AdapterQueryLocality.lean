import OptimalQLS.Refinement.CostedExecution.AdapterQueryLocalityPreparation
import OptimalQLS.Refinement.CostedExecution.AdapterQueryLocalityFilter
import OptimalQLS.Refinement.CostedExecution.AdapterQueryLocalityCorrection
import OptimalQLS.Refinement.CostedExecution.AdapterQueryLocalityVector
/-! # Argument-register placement for the adapter's original oracle queries -/
noncomputable section
namespace OptimalQLS.Refinement.CostedExecution
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
open PhysicalProgram PhysicalMeasurement Reduction PhysicalAdapter
open scoped Classical
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

def adapterMatrixPlacement (a n ℓ : ℕ) (f : PhysicalProgram.Flag) :
    LiteralQueryPlacement (matrixArguments a n) (adapterCoordinates a n ℓ) (originalMatrixPort a n ℓ f) := by
  cases f with
  | preparation => exact ⟨adapterOriginalMatrixFrame a n ℓ .preparation,adapterOriginalPreparationEmbedding a n ℓ⟩
  | filter => exact ⟨adapterDirectFilterFrame a n ℓ,adapterOriginalFilterEmbedding a n ℓ⟩
  | correction => exact ⟨adapterOriginalMatrixFrame a n ℓ .correction,adapterOriginalCorrectionEmbedding a n ℓ⟩

def adapterVectorPlacement (a n ℓ : ℕ) :
    LiteralQueryPlacement (Equiv.refl (Bits n)) (adapterCoordinates a n ℓ) (originalVectorPort a n ℓ) where
  frame := adapterOriginalVectorFrame a n ℓ
  wires := adapterOriginalVectorEmbedding a n ℓ


variable {a n : ℕ} {κ s ŝ ε : ℝ} {h : BudgetParameters κ s ŝ}

theorem adapted_matrixCall_literal_placement
    (I : PhysicalProgram.Implementation a (n+1) (ε := ε) h)
    (p : QueryPort (Bits a × Bits n) (PhysicalAdapter.Space a n (preparationExponent κ)))
    (adj : Bool) (hp : NamedInstruction.matrixCall p adj ∈ adapted I) :
    Nonempty (LiteralQueryPlacement (matrixArguments a n)
      (adapterCoordinates a n (preparationExponent κ)) p) := by
  obtain ⟨f,rfl⟩ := (adapted_safe I).2.1 p adj hp
  exact ⟨adapterMatrixPlacement a n _ f⟩

theorem adapted_vectorCall_literal_placement
    (I : PhysicalProgram.Implementation a (n+1) (ε := ε) h)
    (p : QueryPort (Bits n) (PhysicalAdapter.Space a n (preparationExponent κ)))
    (adj : Bool) (hp : NamedInstruction.vectorCall p adj ∈ adapted I) :
    Nonempty (LiteralQueryPlacement (Equiv.refl (Bits n))
      (adapterCoordinates a n (preparationExponent κ)) p) := by
  rw [(adapted_safe I).2.2 p adj hp]
  exact ⟨adapterVectorPlacement a n _⟩

end OptimalQLS.Refinement.CostedExecution
