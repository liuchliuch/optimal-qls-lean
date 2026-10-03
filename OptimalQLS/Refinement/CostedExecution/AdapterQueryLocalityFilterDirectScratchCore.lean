import OptimalQLS.Refinement.CostedExecution.AdapterQueryLocalityFilterDirectCore
noncomputable section
namespace OptimalQLS.Refinement.CostedExecution
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
open PhysicalProgram PhysicalMeasurement Reduction PhysicalAdapter
open scoped Classical
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 600000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false

theorem adapterDirectFilter_scratch (a n ℓ : ℕ)
    (v : Bool × (Bits a × Bits n)) (r : (adapterDirectFilterFrame a n ℓ).Rest) :
    ((adapterDirectFilterFrame a n ℓ).wiring (v,r)).2 =
      (r.1.1,v.1,r.1.2 ⟨.inr 1,by decide⟩) := by
  change (r.1.1,(Equiv.funSplitAt (smallTarget 2) Bool).symm (v.1,r.1.2) (.inr 0),
    (Equiv.funSplitAt (smallTarget 2) Bool).symm (v.1,r.1.2) (.inr 1)) = _
  simp only [Equiv.funSplitAt_symm_apply,smallTarget,↓reduceDIte,Fin.reduceEq,Sum.inr.injEq]

end OptimalQLS.Refinement.CostedExecution
