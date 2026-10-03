import OptimalQLS.Reduction.PhysicalAdapter.Frames

/-! Explicit placements on the three existing flags and one shared scratch register. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.Reduction.PhysicalAdapter
open Matrix PolynomialTransform TransducerCompiler BinaryClock Refinement

def matrixPort (a n ℓ : ℕ) : Refinement.PhysicalProgram.Flag → QueryPort (Bits a × Bits n) (Refinement.PhysicalProgram.Register a n ℓ)
  | .preparation => Refinement.PhysicalProgram.preparationMatrixPort a n ℓ
  | .filter => Refinement.PhysicalProgram.filterMatrixPort a n ℓ
  | .correction => Refinement.PhysicalProgram.correctionMatrixPort a n ℓ

def matrixFrameRaw (a n ℓ : ℕ) (f : Refinement.PhysicalProgram.Flag) : ControlFrame (matrixPort a n ℓ f) := by
  cases f with
  | preparation => exact ((singleFlagFrame GraphEncoding.flagWire).lift
      (scratchPort (Preparation.CompilerAttachment.graphFrame a n ℓ)) (fun _=>rfl)).lift (Refinement.PhysicalProgram.preparationPort a n ℓ) (fun _=>rfl)
  | filter => exact ((singleFlagFrame GraphEncoding.flagWire).lift
      (relabelPort (graphAttachWiring a (Bits n))) (fun _=>rfl)).lift filterPort (fun _=>rfl)
  | correction => exact ((singleFlagFrame (DirtyAncilla.smallTarget 2)).lift
      (relabelPort (oracleAttachWiring a (Bits n))) (fun _=>rfl)).lift correctionPort (fun _=>rfl)

def vectorFrameRaw (a n ℓ : ℕ) : ControlFrame (Refinement.PhysicalProgram.preparationVectorPort a n ℓ) :=
  ((singleFlagFrame (DirtyAncilla.smallTarget 2)).lift
    (scratchPort (Preparation.CompilerAttachment.vectorFrame a n ℓ)) (fun _=>rfl)).lift (Refinement.PhysicalProgram.preparationPort a n ℓ) (fun _=>rfl)

def matrixCoordinates (a n : ℕ) : Bits a × Bits (n+1) ≃ Bits a × (Bits n ⊕ Bits n) :=
  Equiv.prodCongr (Equiv.refl _) (sumBits n)

def matrixFrame (a n ℓ : ℕ) (f : Refinement.PhysicalProgram.Flag) :=
  (matrixFrameRaw a (n+1) ℓ f).coordinates (matrixCoordinates a n)

def vectorFrame (a n ℓ : ℕ) := (vectorFrameRaw a (n+1) ℓ).coordinates (sumBits n)

abbrev Space (a n ℓ : ℕ) := Refinement.PhysicalProgram.Register a (n+1) ℓ × PhaseScratch

def clean (a n ℓ : ℕ) (x : Refinement.PhysicalProgram.Register a (n+1) ℓ) : Space a n ℓ :=
  (x,(false,false,false))

theorem clean_isometry (a n ℓ : ℕ) :
    (basisInsertion (clean a n ℓ))ᴴ*basisInsertion (clean a n ℓ)=1 :=
  basisInsertion_isometry _ (fun _ _ h=>congrArg Prod.fst h)

/-- Full local wiring, including all three scratch wires, not only the clean image. -/
def dilationFull (S D : Type) : DilationSpace (S × D) ≃
    (Bool × (S × (D ⊕ D))) × PhaseScratch :=
  (oracleLocalWiring (S × D)).trans
    (Equiv.prodCongr ((dilationLogicalWiring (S × D)).trans (dilationSignalLogicalWiring S D))
      (Equiv.refl _))

def vectorFull (D : Type) : DilationSpace D ≃ (Bool × (D ⊕ D)) × PhaseScratch :=
  (oracleLocalWiring D).trans (Equiv.prodCongr (dilationLogicalWiring D) (Equiv.refl _))

@[simp] theorem dilationFull_clean {S D : Type} (x : Bool × (S × (D ⊕ D))) :
    dilationFull S D (dilationSignalClean x)=(x,(false,false,false)) := by
  simp [dilationFull,dilationSignalClean,dilationSumClean,dilationClean,oracleLocalClean]

@[simp] theorem vectorFull_clean {D : Type} (x : Bool × (D ⊕ D)) :
    vectorFull D (dilationSumClean x)=(x,(false,false,false)) := by
  simp [vectorFull,dilationSumClean,dilationClean,oracleLocalClean]

def matrixWiring (a n ℓ : ℕ) (f : Refinement.PhysicalProgram.Flag) :
    DilationSpace (Bits a × Bits n) × (matrixFrame a n ℓ f).Rest ≃ Space a n ℓ :=
  (Equiv.prodCongr (dilationFull (Bits a) (Bits n)) (Equiv.refl _)).trans
    (Preparation.CompilerAttachment.scratchFrame (matrixFrame a n ℓ f).wiring)

def vectorWiring (a n ℓ : ℕ) :
    DilationSpace (Bits n) × (vectorFrame a n ℓ).Rest ≃ Space a n ℓ :=
  (Equiv.prodCongr (vectorFull (Bits n)) (Equiv.refl _)).trans
    (Preparation.CompilerAttachment.scratchFrame (vectorFrame a n ℓ).wiring)

@[simp] theorem matrixWiring_clean (a n ℓ : ℕ) (f : Refinement.PhysicalProgram.Flag)
    (x : Bool × (Bits a × (Bits n ⊕ Bits n))) (r : (matrixFrame a n ℓ f).Rest) :
    matrixWiring a n ℓ f (dilationSignalClean x,r)=clean a n ℓ ((matrixFrame a n ℓ f).wiring (x,r)) := by
  simp [matrixWiring,Preparation.CompilerAttachment.scratchFrame,clean]

@[simp] theorem vectorWiring_clean (a n ℓ : ℕ)
    (x : Bool × (Bits n ⊕ Bits n)) (r : (vectorFrame a n ℓ).Rest) :
    vectorWiring a n ℓ (dilationSumClean x,r)=clean a n ℓ ((vectorFrame a n ℓ).wiring (x,r)) := by
  simp [vectorWiring,Preparation.CompilerAttachment.scratchFrame,clean]

end OptimalQLS.Reduction.PhysicalAdapter
