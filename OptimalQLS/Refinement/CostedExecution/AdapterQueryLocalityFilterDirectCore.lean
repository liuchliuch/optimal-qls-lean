import OptimalQLS.Refinement.CostedExecution.AdapterQueryLocalityFilterTransport
noncomputable section
namespace OptimalQLS.Refinement.CostedExecution
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
open PhysicalProgram PhysicalMeasurement Reduction PhysicalAdapter
open scoped Classical
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false

/-- Tensor spectators retain their own type; an extra enumeration is unnecessary. -/
def ControlFrame.direct_lift {A Q P R : Type} [Fintype A] [DecidableEq A]
    [Fintype Q] [DecidableEq Q] [Fintype P] [DecidableEq P]
    [Fintype R] [DecidableEq R] {p : QueryPort A Q}
    (F : ControlFrame p) (e : Q × R ≃ P) : ControlFrame ((scratchPort e).comp p) where
  Rest := F.Rest × R
  wiring := tensorFrame F.wiring e
  correct U := by rw [QueryPort.comp_apply,scratchPort_apply,F.correct,placeHom_comp]

def adapterDirectFilterFrame (a n ℓ : ℕ) : ControlFrame (originalMatrixPort a n ℓ .filter) :=
  OptimalQLS.Refinement.CostedExecution.ControlFrame.direct_lift
    (singleFlagFrame (A := Bits a × Bits n) (smallTarget 2)) (matrixWiring a n ℓ .filter)

theorem adapterDirectFilter_formula (a n ℓ : ℕ)
    (v : Bool × (Bits a × Bits n)) (r : (adapterDirectFilterFrame a n ℓ).Rest) :
    (adapterDirectFilterFrame a n ℓ).wiring (v,r) =
      ((matrixFrameRaw a (n+1) ℓ .filter).wiring
        ((r.1.2 ⟨.inl 0,by decide⟩,
          (v.2.1,Fin.cons (r.1.2 ⟨.inl 1,by decide⟩) v.2.2)),r.2),
        (r.1.1,v.1,r.1.2 ⟨.inr 1,by decide⟩)) := by
  change adapterMatrixFrame a n ℓ .filter
    ((r.1.1,(Equiv.funSplitAt (smallTarget 2) Bool).symm (v.1,r.1.2)),(v.2,r.2)) = _
  rw [adapterMatrixFrame_apply]
  simp only [Equiv.funSplitAt_symm_apply,smallTarget,Sum.inl_ne_inr,↓reduceDIte,
    Fin.reduceEq,Sum.inr.injEq]


end OptimalQLS.Refinement.CostedExecution
