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

def adapterOriginalVectorEmbedding (a n ℓ : ℕ) :
    WireEmbedding (productBits boolCoordinates (Equiv.refl (Bits n))) (adapterCoordinates a n ℓ)
      (adapterOriginalVectorFrame a n ℓ).wiring := by
  refine ⟨⟨adapterOriginalVectorWire a n ℓ,adapterOriginalVectorWire_injective a n ℓ⟩,?_,?_⟩
  · intro x r i
    rw [adapterOriginalVectorFrame_apply,adapterVectorFrame_apply,preparation_vectorFrameRaw_wiring]
    cases i <;> adapter_query_wire
  · intro x y r j hj
    rw [adapterOriginalVectorFrame_apply,adapterOriginalVectorFrame_apply,adapterVectorFrame_apply,adapterVectorFrame_apply,preparation_vectorFrameRaw_wiring,preparation_vectorFrameRaw_wiring]
    rcases j with (j|j)
    · rcases j with (j|j)
      · rcases j with (j|j)
        · adapter_query_wire
        · rcases j with (j|j)
          · rcases j with (j|j)
            · adapter_query_wire
            · rcases j with (j|j)
              · adapter_query_wire
              · rcases j with (j|j)
                · exact False.elim (hj (.inl ()) (by cases j; rfl))
                · adapter_query_wire
          · adapter_query_wire
      · revert hj
        refine Fin.cases (fun hj=>?_) (fun j hj=>?_) j
        · adapter_query_wire
        · exact False.elim (hj (.inr j) rfl)


    · adapter_query_wire

end OptimalQLS.Refinement.CostedExecution
