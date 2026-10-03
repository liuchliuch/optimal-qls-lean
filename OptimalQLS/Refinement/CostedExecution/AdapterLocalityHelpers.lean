import OptimalQLS.Refinement.CostedExecution.Locality
import OptimalQLS.Reduction.PhysicalAdapter.Complete

/-! # Literal full-bit tensor frames of the physical dilation adapter -/
noncomputable section
namespace OptimalQLS.Refinement.CostedExecution
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
open PhysicalProgram PhysicalMeasurement
open Reduction PhysicalAdapter
open scoped Classical
local instance : Nonempty Label := ⟨.pub⟩
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

abbrev AdapterScratchWire := Unit ⊕ (Unit ⊕ Unit)
abbrev AdapterWire (a n ℓ : ℕ) := FullWire a (n+1) ℓ ⊕ AdapterScratchWire

def adapterCoordinates (a n ℓ : ℕ) : PhysicalAdapter.Space a n ℓ ≃ (AdapterWire a n ℓ → Bool) :=
  productBits (registerCoordinates a (n+1) ℓ).symm
    (productBits boolCoordinates (productBits boolCoordinates boolCoordinates))

def oldRegisterEmbedding (a n ℓ : ℕ) :
    WireEmbedding (registerBits a (n+1) ℓ) (adapterCoordinates a n ℓ)
      (Equiv.refl (PhysicalAdapter.Space a n ℓ)) where
  wire := ⟨Sum.inl,Sum.inl_injective⟩
  read := by intros; rfl
  outside := by
    intro x y r j hj
    cases j with
    | inl j => exact False.elim (hj j rfl)
    | inr j => rfl

def adapterMatrixFrame (a n ℓ : ℕ) (f : PhysicalProgram.Flag) :
    OracleLocalState × ((Bits a × Bits n) × (PhysicalAdapter.matrixFrame a n ℓ f).Rest) ≃
      PhysicalAdapter.Space a n ℓ :=
  tensorFrame (Equiv.refl _) (matrixWiring a n ℓ f)

def adapterVectorFrame (a n ℓ : ℕ) :
    OracleLocalState × (Bits n × (PhysicalAdapter.vectorFrame a n ℓ).Rest) ≃
      PhysicalAdapter.Space a n ℓ :=
  tensorFrame (Equiv.refl _) (vectorWiring a n ℓ)

/-- Dilation replaces only the old control and the literal leading data bit. -/
theorem adapterMatrixFrame_apply (a n ℓ : ℕ) (f : PhysicalProgram.Flag)
    (x : OracleLocalState)
    (r : (Bits a × Bits n) × (PhysicalAdapter.matrixFrame a n ℓ f).Rest) :
    adapterMatrixFrame a n ℓ f (x,r) =
      ((matrixFrameRaw a (n+1) ℓ f).wiring
        ((x.2 (.inl 0),(r.1.1,Fin.cons (x.2 (.inl 1)) r.1.2)),r.2),
        (x.1,x.2 (.inr 0),x.2 (.inr 1))) := by
  cases hb : x.2 (.inl 1) <;>
    simp [adapterMatrixFrame,tensorFrame,matrixWiring,dilationFull,
      CompilerAttachment.scratchFrame,PhysicalAdapter.matrixFrame,ControlFrame.coordinates,
      oracleLocalWiring,dilationLogicalWiring,dilationSignalLogicalWiring,
      matrixCoordinates,sumBits,headTail,GraphEncoding.sumBitWiring,LowerBounds.distributeSignal,hb]
  all_goals
    funext i
    refine Fin.cases ?_ (fun i=>?_) i <;> rfl

theorem adapterVectorFrame_apply (a n ℓ : ℕ) (x : OracleLocalState)
    (r : Bits n × (PhysicalAdapter.vectorFrame a n ℓ).Rest) :
    adapterVectorFrame a n ℓ (x,r) =
      ((vectorFrameRaw a (n+1) ℓ).wiring
        ((x.2 (.inl 0),Fin.cons (x.2 (.inl 1)) r.1),r.2),
        (x.1,x.2 (.inr 0),x.2 (.inr 1))) := by
  cases hb : x.2 (.inl 1) <;>
    simp [adapterVectorFrame,tensorFrame,vectorWiring,vectorFull,
      CompilerAttachment.scratchFrame,PhysicalAdapter.vectorFrame,ControlFrame.coordinates,
      oracleLocalWiring,dilationLogicalWiring,sumBits,headTail,GraphEncoding.sumBitWiring,hb]
  all_goals
    funext i
    refine Fin.cases ?_ (fun i=>?_) i <;> rfl

def adapterMacroWire (a n ℓ : ℕ) (f : PhysicalProgram.Flag) :
    Unit ⊕ OracleLocalWire → AdapterWire a n ℓ
  | .inl _ => .inr (.inl ())
  | .inr (.inl i) => if i=0 then .inl (controlWire a (n+1) ℓ f) else .inl (.inr 0)
  | .inr (.inr i) => .inr (.inr (if i=0 then .inl () else .inr ()))



/-- Expose only the computational wiring, factoring out ControlFrame's proof fields. -/
theorem preparation_matrixFrameRaw_wiring (a n ℓ : ℕ)
    (v : Bool × (Bits a × Bits n)) (r : (matrixFrameRaw a n ℓ .preparation).Rest) :
    (matrixFrameRaw a n ℓ .preparation).wiring (v,r) =
      preparationGraphFrame a n ℓ
        ((r.1.1.1,(Equiv.funSplitAt GraphEncoding.flagWire Bool).symm (v.1,r.1.1.2)),
          (v.2,((Fintype.equivFin (CompilerAttachment.CompilerRest ℓ)).symm r.1.2,
            (Fintype.equivFin (CorrectionSignal a × FilterSignal a)).symm r.2))) := rfl

theorem filter_matrixFrameRaw_wiring (a n ℓ : ℕ)
    (v : Bool × (Bits a × Bits n)) (r : (matrixFrameRaw a n ℓ .filter).Rest) :
    (matrixFrameRaw a n ℓ .filter).wiring (v,r) =
      filterGraphFrame a n ℓ
        ((r.1.1.1,(Equiv.funSplitAt GraphEncoding.flagWire Bool).symm (v.1,r.1.1.2)),
          (v.2,(Fintype.equivFin (CorrectionSignal a × PrepAux a ℓ)).symm r.2)) := rfl

theorem correction_matrixFrameRaw_wiring (a n ℓ : ℕ)
    (v : Bool × (Bits a × Bits n)) (r : (matrixFrameRaw a n ℓ .correction).Rest) :
    (matrixFrameRaw a n ℓ .correction).wiring (v,r) =
      correctionOracleFrame a n ℓ
        ((r.1.1.1,(Equiv.funSplitAt (smallTarget 2) Bool).symm (v.1,r.1.1.2)),
          (v.2,(Fintype.equivFin (PrepAux a ℓ × (FilterSignal a × Fin 4))).symm r.2)) := rfl

theorem preparation_vectorFrameRaw_wiring (a n ℓ : ℕ)
    (v : Bool × Bits n) (r : (vectorFrameRaw a n ℓ).Rest) :
    (vectorFrameRaw a n ℓ).wiring (v,r) =
      preparationOracleFrame a n ℓ
        ((r.1.1.1,(Equiv.funSplitAt (smallTarget 2) Bool).symm (v.1,r.1.1.2)),
          (v.2,((Fintype.equivFin (CompilerAttachment.SourceRest a ℓ)).symm r.1.2,
            (Fintype.equivFin (CorrectionSignal a × FilterSignal a)).symm r.2))) := rfl

end OptimalQLS.Refinement.CostedExecution
