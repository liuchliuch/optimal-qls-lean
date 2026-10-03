import OptimalQLS.Refinement.CostedExecution.QueryLocalityCore
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

def normalizedPreparationMatrixEmbedding (a n ℓ : ℕ) :
    WireEmbedding (productBits boolCoordinates (matrixArguments a n)) (registerBits a n ℓ)
      (matrixFrameRaw a n ℓ .preparation).wiring := by
  refine ⟨⟨normalizedMatrixWire a n ℓ .preparation,normalizedMatrixWire_injective a n ℓ .preparation⟩,?_,?_⟩
  · intro x r i
    rw [preparation_matrixFrameRaw_wiring]
    rcases i with (i|(i|i)) <;> query_wire
  · intro x y r j hj
    rw [preparation_matrixFrameRaw_wiring,preparation_matrixFrameRaw_wiring]
    rcases j with (j|j)
    · rcases j with (j|j)
      · query_wire
      · rcases j with (j|j)
        · rcases j with (j|j)
          · rcases j with (j|j)
            · query_wire
            · rcases j with (j|j)
              · query_wire
              · rcases j with (j|j)
                · rcases j with (j|(j|(j|(j|j))))
                  · query_wire
                  · query_wire
                  · query_wire
                  · query_wire
                  · exact False.elim (hj (.inr (.inl j)) rfl)
                · query_wire
          · rcases j with (j|j)
            · query_wire
            · rcases j with (j|j)
              · exact False.elim (hj (.inl ()) (by cases j; rfl))
              · query_wire
        · query_wire
    · exact False.elim (hj (.inr (.inr j)) rfl)


end OptimalQLS.Refinement.CostedExecution
