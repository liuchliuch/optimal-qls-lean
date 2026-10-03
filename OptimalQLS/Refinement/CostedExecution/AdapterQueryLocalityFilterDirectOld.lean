import OptimalQLS.Refinement.CostedExecution.AdapterQueryLocalityFilterDirectCore
import OptimalQLS.Refinement.CostedExecution.AdapterQueryLocalityFilterProjection
noncomputable section
namespace OptimalQLS.Refinement.CostedExecution
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
open PhysicalProgram PhysicalMeasurement Reduction PhysicalAdapter
open scoped Classical
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false

attribute [local irreducible] normalizedFilterMatrixEmbedding

theorem adapterDirectFilter_outside_old (a n ℓ : ℕ)
    (x y : Bool × (Bits a × Bits n)) (r : (adapterDirectFilterFrame a n ℓ).Rest)
    (j : FullWire a (n+1) ℓ) (hj : ∀ i,adapterOriginalMatrixWire a n ℓ .filter i ≠ .inl j) :
    adapterCoordinates a n ℓ ((adapterDirectFilterFrame a n ℓ).wiring (x,r)) (.inl j) =
      adapterCoordinates a n ℓ ((adapterDirectFilterFrame a n ℓ).wiring (y,r)) (.inl j) := by
  rw [adapterDirectFilter_formula,adapterDirectFilter_formula]
  change registerBits a (n+1) ℓ _ j = registerBits a (n+1) ℓ _ j
  have h := (normalizedFilterMatrixEmbedding a (n+1) ℓ).agree_at
    (r.1.2 ⟨.inl 0,by decide⟩,(x.2.1,Fin.cons (r.1.2 ⟨.inl 1,by decide⟩) x.2.2))
    (r.1.2 ⟨.inl 0,by decide⟩,(y.2.1,Fin.cons (r.1.2 ⟨.inl 1,by decide⟩) y.2.2))
    r.2 j
  apply h
  intro i hi
  rw [normalizedFilterMatrixEmbedding_wire] at hi
  rcases i with (i|(i|i))
  · rfl
  · exact False.elim (hj (.inr (.inl i)) (congrArg Sum.inl hi))
  · revert hi
    refine Fin.cases (fun hi=>?_) (fun i hi=>?_) i
    · rfl
    · exact False.elim (hj (.inr (.inr i)) (congrArg Sum.inl hi))

end OptimalQLS.Refinement.CostedExecution
