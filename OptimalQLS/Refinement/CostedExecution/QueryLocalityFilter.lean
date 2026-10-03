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

def normalizedFilterMatrixEmbedding (a n ℓ : ℕ) :
    WireEmbedding (productBits boolCoordinates (matrixArguments a n)) (registerBits a n ℓ)
      (matrixFrameRaw a n ℓ .filter).wiring := by
  refine ⟨⟨normalizedMatrixWire a n ℓ .filter,normalizedMatrixWire_injective a n ℓ .filter⟩,?_,?_⟩
  · intro x r i
    rw [filter_matrixFrameRaw_wiring]
    rcases i with (i|(i|i)) <;> query_wire
  · intro x y r j hj
    rw [filter_matrixFrameRaw_wiring,filter_matrixFrameRaw_wiring]
    rcases j with (j|j)
    · rcases j with (j|j)
      · query_wire
      · rcases j with (j|j)
        · query_wire
        · rcases j with (j|j)
          · rcases j with (j|(j|j))
            · query_wire
            · revert hj
              refine Fin.cases (fun hj=>?_) (fun j hj=>?_) j
              · query_wire
              · revert hj
                refine Fin.cases (fun hj=>?_) (fun j hj=>?_) j
                · query_wire
                · revert hj
                  refine Fin.cases (fun hj=>?_) (fun j hj=>?_) j
                  · query_wire
                  · revert hj
                    refine Fin.cases (fun hj=>?_) (fun j hj=>?_) j
                    · query_wire
                    · exact False.elim (hj (.inr (.inl j)) rfl)
            · fin_cases j
              · query_wire
              · query_wire
              · exact False.elim (hj (.inl ()) rfl)
              · query_wire
          · query_wire
    · exact False.elim (hj (.inr (.inr j)) rfl)


end OptimalQLS.Refinement.CostedExecution
