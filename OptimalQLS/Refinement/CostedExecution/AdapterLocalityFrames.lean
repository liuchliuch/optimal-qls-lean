import OptimalQLS.Refinement.CostedExecution.AdapterLocalityPreparation
import OptimalQLS.Refinement.CostedExecution.AdapterLocalityFilter
import OptimalQLS.Refinement.CostedExecution.AdapterLocalityCorrection
import OptimalQLS.Refinement.CostedExecution.AdapterLocalityVector
/-! # Literal full-bit tensor frames of the physical dilation adapter -/
noncomputable section
namespace OptimalQLS.Refinement.CostedExecution
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
open PhysicalProgram PhysicalMeasurement
open Reduction PhysicalAdapter
open scoped Classical
local instance : Nonempty Label := ⟨.pub⟩
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false


def adapterMatrixEmbedding (a n ℓ : ℕ) (f : PhysicalProgram.Flag) :
    WireEmbedding phaseBits (adapterCoordinates a n ℓ) (adapterMatrixFrame a n ℓ f) := by
  cases f with
  | preparation => exact preparationAdapterEmbedding a n ℓ
  | filter => exact filterAdapterEmbedding a n ℓ
  | correction => exact correctionAdapterEmbedding a n ℓ


end OptimalQLS.Refinement.CostedExecution
