import OptimalQLS.Refinement.CostedExecution.QueryLocalityPreparation
import OptimalQLS.Refinement.CostedExecution.QueryLocalityFilter
import OptimalQLS.Refinement.CostedExecution.QueryLocalityCorrection
import OptimalQLS.Refinement.CostedExecution.QueryLocalityVector
/-! # Literal physical placement of the original oracle argument registers

A single-bit readout alone is insufficient: this certificate also exposes every
argument qubit and proves that every unselected physical bit is a spectator. -/
noncomputable section
namespace OptimalQLS.Refinement.CostedExecution
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
open PhysicalProgram PhysicalMeasurement
open Reduction PhysicalAdapter
open scoped Classical
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

def normalizedMatrixPlacement (a n ℓ : ℕ) (f : PhysicalProgram.Flag) :
    LiteralQueryPlacement (matrixArguments a n) (registerBits a n ℓ) (matrixPort a n ℓ f) where
  frame := matrixFrameRaw a n ℓ f
  wires := by
    cases f with
    | preparation => exact normalizedPreparationMatrixEmbedding a n ℓ
    | filter => exact normalizedFilterMatrixEmbedding a n ℓ
    | correction => exact normalizedCorrectionMatrixEmbedding a n ℓ

def normalizedVectorPlacement (a n ℓ : ℕ) :
    LiteralQueryPlacement (Equiv.refl (Bits n)) (registerBits a n ℓ)
      (PhysicalProgram.preparationVectorPort a n ℓ) where
  frame := vectorFrameRaw a n ℓ
  wires := normalizedVectorEmbedding a n ℓ


variable {a n : ℕ} {κ s ŝ ε : ℝ} {h : BudgetParameters κ s ŝ}

theorem Implementation.matrixCall_literal_placement
    (I : PhysicalProgram.Implementation a n (ε := ε) h)
    (p : QueryPort (Bits a × Bits n) (Register a n (preparationExponent κ)))
    (adj : Bool) (hp : NamedInstruction.matrixCall p adj ∈ I.circuit) :
    Nonempty (LiteralQueryPlacement (matrixArguments a n)
      (registerBits a n (preparationExponent κ)) p) := by
  rcases program_matrix_ports a n _ I.preparation I.preparation_strict I.filter I.filter_ports
    I.correction I.correction_ports p adj hp with rfl|rfl|rfl
  · exact ⟨normalizedMatrixPlacement a n _ .preparation⟩
  · exact ⟨normalizedMatrixPlacement a n _ .filter⟩
  · exact ⟨normalizedMatrixPlacement a n _ .correction⟩

theorem Implementation.vectorCall_literal_placement
    (I : PhysicalProgram.Implementation a n (ε := ε) h)
    (p : QueryPort (Bits n) (Register a n (preparationExponent κ)))
    (adj : Bool) (hp : NamedInstruction.vectorCall p adj ∈ I.circuit) :
    Nonempty (LiteralQueryPlacement (Equiv.refl (Bits n))
      (registerBits a n (preparationExponent κ)) p) := by
  rw [program_vector_ports a n _ I.preparation I.preparation_strict I.filter I.filter_vector
    I.correction I.correction_vector p adj hp]
  exact ⟨normalizedVectorPlacement a n _⟩

end OptimalQLS.Refinement.CostedExecution
