import OptimalQLS.Refinement.CostedExecution.QueryLocalityFilter
noncomputable section
namespace OptimalQLS.Refinement.CostedExecution
open PhysicalProgram PhysicalMeasurement

theorem normalizedFilterMatrixEmbedding_wire (a n ℓ : ℕ) (i : Unit ⊕ (Fin a ⊕ Fin n)) :
    (normalizedFilterMatrixEmbedding a n ℓ).wire i = normalizedMatrixWire a n ℓ .filter i := rfl

end OptimalQLS.Refinement.CostedExecution
