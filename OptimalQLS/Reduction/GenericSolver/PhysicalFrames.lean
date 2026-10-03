import OptimalQLS.TransducerCompiler.Physical.Basic
import OptimalQLS.Refinement.CostedExecution.RealLocality
import OptimalQLS.Reduction.PhysicalAdapter.Placement

/-! Generic physical oracle-call layouts. The source work gates are arbitrary
one/two-qubit gates. Every oracle call may choose its own literal target/control
wire placement; the shared three scratch wires are included in the layout.
The layout witnesses contain only coordinate identities, never circuit accuracy. -/
noncomputable section
open scoped Classical
namespace OptimalQLS.Reduction.GenericSolver.Physical
open Matrix TransducerCompiler BinaryClock PolynomialTransform
open Refinement.CostedExecution Refinement.PhysicalMeasurement
open Preparation.CompilerAttachment
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 700000
set_option maxRecDepth 4096

abbrev ScratchWire := Unit ⊕ (Unit ⊕ Unit)
def scratchCoordinates : PhaseScratch ≃ (ScratchWire → Bool) :=
  productBits boolCoordinates (productBits boolCoordinates boolCoordinates)
def coordinates {P W : Type} (chart : P ≃ (W → Bool)) :
    P × PhaseScratch ≃ ((W ⊕ ScratchWire) → Bool) :=
  productBits chart scratchCoordinates

def clean {P : Type} (x : P) : P × PhaseScratch := (x,(false,false,false))

def matrixWiring {P R : Type} (a n : ℕ)
    (frame : (Bool × (Bits a × (Bits n ⊕ Bits n))) × R ≃ P) :
    DilationSpace (Bits a × Bits n) × R ≃ P × PhaseScratch :=
  (Equiv.prodCongr (PhysicalAdapter.dilationFull (Bits a) (Bits n)) (Equiv.refl _)).trans
    (scratchFrame frame)

def vectorWiring {P R : Type} (n : ℕ)
    (frame : (Bool × (Bits n ⊕ Bits n)) × R ≃ P) :
    DilationSpace (Bits n) × R ≃ P × PhaseScratch :=
  (Equiv.prodCongr (PhysicalAdapter.vectorFull (Bits n)) (Equiv.refl _)).trans
    (scratchFrame frame)

def matrixCoordinates (a n : ℕ) : DilationSpace (Bits a × Bits n) ≃
    (((Unit ⊕ DilationWire) ⊕ (Fin a ⊕ Fin n)) → Bool) :=
  productBits (phaseCoordinates _) (productBits (Equiv.refl _) (Equiv.refl _))
def vectorCoordinates (n : ℕ) : DilationSpace (Bits n) ≃
    (((Unit ⊕ DilationWire) ⊕ Fin n) → Bool) :=
  productBits (phaseCoordinates _) (Equiv.refl _)

structure MatrixFrame {P W : Type} (chart : P ≃ (W → Bool)) (a n : ℕ) where
  Rest : Type
  [finiteRest : Fintype Rest]
  [decidableRest : DecidableEq Rest]
  frame : (Bool × (Bits a × (Bits n ⊕ Bits n))) × Rest ≃ P
  wires : WireEmbedding (matrixCoordinates a n) (coordinates chart) (matrixWiring a n frame)
structure VectorFrame {P W : Type} (chart : P ≃ (W → Bool)) (n : ℕ) where
  Rest : Type
  [finiteRest : Fintype Rest]
  [decidableRest : DecidableEq Rest]
  frame : (Bool × (Bits n ⊕ Bits n)) × Rest ≃ P
  wires : WireEmbedding (vectorCoordinates n) (coordinates chart) (vectorWiring n frame)
attribute [instance] MatrixFrame.finiteRest MatrixFrame.decidableRest
attribute [instance] VectorFrame.finiteRest VectorFrame.decidableRest

variable {P W : Type} [Fintype P] [DecidableEq P]
  {chart : P ≃ (W → Bool)} {a n : ℕ}

def MatrixFrame.port (F : MatrixFrame chart a n) : QueryPort (Bits a × (Bits n ⊕ Bits n)) P :=
  (scratchPort F.frame).comp (bitControlPort _)
def VectorFrame.port (F : VectorFrame chart n) : QueryPort (Bits n ⊕ Bits n) P :=
  (scratchPort F.frame).comp (bitControlPort _)

theorem MatrixFrame.port_apply (F : MatrixFrame chart a n)
    (U : Matrix.unitaryGroup (Bits a × (Bits n ⊕ Bits n)) ℂ) :
    F.port.apply U=GateSynthesis.placeHom F.frame ((bitControlPort _).apply U) := by
  rw [MatrixFrame.port,QueryPort.comp_apply,scratchPort_apply]
theorem VectorFrame.port_apply (F : VectorFrame chart n)
    (U : Matrix.unitaryGroup (Bits n ⊕ Bits n) ℂ) :
    F.port.apply U=GateSynthesis.placeHom F.frame ((bitControlPort _).apply U) := by
  rw [VectorFrame.port,QueryPort.comp_apply,scratchPort_apply]

def oldEmbedding : WireEmbedding chart (coordinates chart) (Equiv.refl (P × PhaseScratch)) where
  wire := Function.Embedding.inl
  read := by intros; rfl
  outside := by
    intro x y r j hj
    cases j with
    | inl j => exact False.elim (hj j rfl)
    | inr j => rfl

def phaseMatrixEmbedding (a n : ℕ) : WireEmbedding phaseBits (matrixCoordinates a n)
    (Equiv.refl (DilationSpace (Bits a × Bits n))) where
  wire := Function.Embedding.inl
  read := by intros; rfl
  outside := by
    intro x y r j hj
    cases j with
    | inl j => exact False.elim (hj j rfl)
    | inr j => rfl

def phaseVectorEmbedding (n : ℕ) : WireEmbedding phaseBits (vectorCoordinates n)
    (Equiv.refl (DilationSpace (Bits n))) where
  wire := Function.Embedding.inl
  read := by intros; rfl
  outside := by
    intro x y r j hj
    cases j with
    | inl j => exact False.elim (hj j rfl)
    | inr j => rfl

theorem clean_isometry : (basisInsertion (clean (P := P)))ᴴ*basisInsertion (clean (P := P))=1 :=
  basisInsertion_isometry _ (fun _ _ he => congrArg Prod.fst he)

theorem space_card [Fintype W] (chart : P ≃ (W → Bool)) : Fintype.card (P × PhaseScratch)=2^(Fintype.card W+3) := by
  have hp : Fintype.card P=2^Fintype.card W := by
    rw [Fintype.card_congr chart,Fintype.card_fun,Fintype.card_bool]
  rw [Fintype.card_prod,hp]
  have hs : Fintype.card PhaseScratch=2^3 := by decide
  rw [hs,←pow_add]

end OptimalQLS.Reduction.GenericSolver.Physical
