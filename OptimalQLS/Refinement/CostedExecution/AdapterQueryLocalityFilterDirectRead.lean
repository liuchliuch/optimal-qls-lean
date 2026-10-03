import OptimalQLS.Refinement.CostedExecution.AdapterQueryLocalityFilterDirectCore
noncomputable section
namespace OptimalQLS.Refinement.CostedExecution
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
open PhysicalProgram PhysicalMeasurement Reduction PhysicalAdapter
open scoped Classical
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false

theorem adapterDirectFilter_read (a n ℓ : ℕ)
    (x : Bool × (Bits a × Bits n)) (r : (adapterDirectFilterFrame a n ℓ).Rest)
    (i : Unit ⊕ (Fin a ⊕ Fin n)) :
    adapterCoordinates a n ℓ ((adapterDirectFilterFrame a n ℓ).wiring (x,r))
      (adapterOriginalMatrixWire a n ℓ .filter i) =
        productBits boolCoordinates (matrixArguments a n) x i := by
  rw [adapterDirectFilter_formula]
  rcases i with (i|(i|i))
  · cases i; rfl
  · exact (normalizedFilterMatrixEmbedding a (n+1) ℓ).read _ r.2 (.inr (.inl i))
  · exact (normalizedFilterMatrixEmbedding a (n+1) ℓ).read _ r.2 (.inr (.inr i.succ))

end OptimalQLS.Refinement.CostedExecution
