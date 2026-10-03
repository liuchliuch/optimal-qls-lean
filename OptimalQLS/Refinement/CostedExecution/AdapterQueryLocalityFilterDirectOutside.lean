import OptimalQLS.Refinement.CostedExecution.AdapterQueryLocalityFilterDirectOld
import OptimalQLS.Refinement.CostedExecution.AdapterQueryLocalityFilterDirectScratch
noncomputable section
namespace OptimalQLS.Refinement.CostedExecution
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
open PhysicalProgram PhysicalMeasurement Reduction PhysicalAdapter
open scoped Classical
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false

theorem adapterDirectFilter_outside (a n ℓ : ℕ)
    (x y : Bool × (Bits a × Bits n)) (r : (adapterDirectFilterFrame a n ℓ).Rest)
    (j : AdapterWire a n ℓ) (hj : ∀ i,adapterOriginalMatrixWire a n ℓ .filter i ≠ j) :
    adapterCoordinates a n ℓ ((adapterDirectFilterFrame a n ℓ).wiring (x,r)) j =
      adapterCoordinates a n ℓ ((adapterDirectFilterFrame a n ℓ).wiring (y,r)) j := by
  cases j with
  | inl j => exact adapterDirectFilter_outside_old a n ℓ x y r j hj
  | inr j => exact adapterDirectFilter_outside_scratch a n ℓ x y r j hj

end OptimalQLS.Refinement.CostedExecution
