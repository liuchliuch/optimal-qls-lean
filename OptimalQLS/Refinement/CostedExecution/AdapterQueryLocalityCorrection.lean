import OptimalQLS.Refinement.CostedExecution.AdapterQueryLocalityCore
/-! # Argument-register placement for the adapter's original oracle queries -/
noncomputable section
namespace OptimalQLS.Refinement.CostedExecution
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
open PhysicalProgram PhysicalMeasurement Reduction PhysicalAdapter
open scoped Classical
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false

def adapterOriginalCorrectionEmbedding (a n ℓ : ℕ) :
    WireEmbedding (productBits boolCoordinates (matrixArguments a n)) (adapterCoordinates a n ℓ)
      (adapterOriginalMatrixFrame a n ℓ .correction).wiring := by
  refine ⟨⟨adapterOriginalMatrixWire a n ℓ .correction,adapterOriginalMatrixWire_injective a n ℓ .correction⟩,?_,?_⟩
  · intro x r i
    rw [adapterOriginalMatrixFrame_apply,adapterMatrixFrame_apply,correction_matrixFrameRaw_wiring]
    rcases i with (i|(i|i)) <;> adapter_query_wire
  · intro x y r j hj
    rw [adapterOriginalMatrixFrame_apply,adapterOriginalMatrixFrame_apply,adapterMatrixFrame_apply,adapterMatrixFrame_apply,correction_matrixFrameRaw_wiring,correction_matrixFrameRaw_wiring]
    rcases j with (j|j)
    · rcases j with (j|j)
      · rcases j with (j|j)
        · rcases j with (j|(j|j))
          · adapter_query_wire
          · exact False.elim (hj (.inr (.inl j)) rfl)
          · fin_cases j
            · adapter_query_wire
            · adapter_query_wire
            · adapter_query_wire
            · adapter_query_wire
        · adapter_query_wire
      · revert hj
        refine Fin.cases (fun hj=>?_) (fun j hj=>?_) j
        · adapter_query_wire
        · exact False.elim (hj (.inr (.inr j)) rfl)


    · rcases j with (j|(j|j))
      · adapter_query_wire
      · exact False.elim (hj (.inl ()) (by cases j; rfl))
      · adapter_query_wire

end OptimalQLS.Refinement.CostedExecution
