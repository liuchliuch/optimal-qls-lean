import OptimalQLS.Refinement.CostedExecution.AdapterQueryLocalityFilterDirectScratchCore
noncomputable section
namespace OptimalQLS.Refinement.CostedExecution
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
open PhysicalProgram PhysicalMeasurement Reduction PhysicalAdapter
open scoped Classical
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false

theorem adapterDirectFilter_outside_scratch (a n ℓ : ℕ)
    (x y : Bool × (Bits a × Bits n)) (r : (adapterDirectFilterFrame a n ℓ).Rest)
    (j : AdapterScratchWire) (hj : ∀ i,adapterOriginalMatrixWire a n ℓ .filter i ≠ .inr j) :
    adapterCoordinates a n ℓ ((adapterDirectFilterFrame a n ℓ).wiring (x,r)) (.inr j) =
      adapterCoordinates a n ℓ ((adapterDirectFilterFrame a n ℓ).wiring (y,r)) (.inr j) := by
  change (productBits boolCoordinates (productBits boolCoordinates boolCoordinates))
    (((adapterDirectFilterFrame a n ℓ).wiring (x,r)).2) j =
      (productBits boolCoordinates (productBits boolCoordinates boolCoordinates))
        (((adapterDirectFilterFrame a n ℓ).wiring (y,r)).2) j
  rw [adapterDirectFilter_scratch,adapterDirectFilter_scratch]
  rcases j with (j|(j|j))
  · rfl
  · exact False.elim (hj (.inl ()) (by cases j; rfl))
  · rfl

end OptimalQLS.Refinement.CostedExecution
