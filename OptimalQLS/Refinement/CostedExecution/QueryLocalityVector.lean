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

def normalizedVectorEmbedding (a n ℓ : ℕ) :
    WireEmbedding (productBits boolCoordinates (Equiv.refl (Bits n))) (registerBits a n ℓ)
      (vectorFrameRaw a n ℓ).wiring := by
  refine ⟨⟨normalizedVectorWire a n ℓ,normalizedVectorWire_injective a n ℓ⟩,?_,?_⟩
  · intro x r i
    rw [preparation_vectorFrameRaw_wiring]
    cases i <;> query_wire
  · intro x y r j hj
    rw [preparation_vectorFrameRaw_wiring,preparation_vectorFrameRaw_wiring]
    rcases j with (j|j)
    · rcases j with (j|j)
      · query_wire
      · rcases j with (j|j)
        · rcases j with (j|j)
          · query_wire
          · rcases j with (j|j)
            · query_wire
            · rcases j with (j|j)
              · exact False.elim (hj (.inl ()) (by cases j; rfl))
              · query_wire
        · query_wire
    · exact False.elim (hj (.inr j) rfl)


end OptimalQLS.Refinement.CostedExecution
