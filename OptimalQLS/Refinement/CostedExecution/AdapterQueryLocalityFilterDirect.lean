import OptimalQLS.Refinement.CostedExecution.AdapterQueryLocalityFilterDirectRead
import OptimalQLS.Refinement.CostedExecution.AdapterQueryLocalityFilterDirectOutside
noncomputable section
namespace OptimalQLS.Refinement.CostedExecution
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
open PhysicalProgram PhysicalMeasurement Reduction PhysicalAdapter
open scoped Classical
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false

def adapterOriginalFilterEmbedding (a n ℓ : ℕ) :
    WireEmbedding (productBits boolCoordinates (matrixArguments a n)) (adapterCoordinates a n ℓ)
      (adapterDirectFilterFrame a n ℓ).wiring where
  wire := ⟨adapterOriginalMatrixWire a n ℓ .filter,adapterOriginalMatrixWire_injective a n ℓ .filter⟩
  read := adapterDirectFilter_read a n ℓ
  outside := adapterDirectFilter_outside a n ℓ

end OptimalQLS.Refinement.CostedExecution
