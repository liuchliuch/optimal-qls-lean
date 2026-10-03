import OptimalQLS.Refinement.CostedExecution.AdapterLocalityHelpers

/-! # Literal physical placement of the original oracle argument registers

A single-bit readout alone is insufficient: this certificate also exposes every
argument qubit and proves that every unselected physical bit is a spectator. -/
noncomputable section
namespace OptimalQLS.Refinement.CostedExecution
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
open PhysicalProgram PhysicalMeasurement
open Reduction PhysicalAdapter
open scoped Classical
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

/-- Exact controlled-oracle semantics plus literal wire placement of control
and every original argument bit. The unitary argument remains arbitrary. -/
structure LiteralQueryPlacement {A P V W : Type} [Fintype A] [DecidableEq A]
    [Fintype P] [DecidableEq P] (arguments : A ≃ (V → Bool))
    (coordinates : P → W → Bool) (p : QueryPort A P) where
  frame : ControlFrame p
  wires : WireEmbedding (productBits boolCoordinates arguments) coordinates frame.wiring

def matrixArguments (a n : ℕ) : Bits a × Bits n ≃ ((Fin a ⊕ Fin n) → Bool) :=
  productBits (Equiv.refl _) (Equiv.refl _)

def normalizedSignalWire (a n ℓ : ℕ) : PhysicalProgram.Flag → Fin a → FullWire a n ℓ
  | .preparation, i => preparationWire a n ℓ (prepGraphWire a ℓ (.inr (.inr (.inr (.inr i)))))
  | .filter, i => filterQspWire a n ℓ (.inr (.inl i.succ.succ.succ.succ))
  | .correction, i => correctionQspWire a n ℓ (.inr (.inl i))

def normalizedMatrixWire (a n ℓ : ℕ) (f : PhysicalProgram.Flag) :
    Unit ⊕ (Fin a ⊕ Fin n) → FullWire a n ℓ
  | .inl _ => controlWire a n ℓ f
  | .inr (.inl i) => normalizedSignalWire a n ℓ f i
  | .inr (.inr i) => .inr i

theorem normalizedMatrixWire_injective (a n ℓ : ℕ) (f : PhysicalProgram.Flag) :
    Function.Injective (normalizedMatrixWire a n ℓ f) := by
  intro i j hij
  cases f <;> rcases i with (i|(i|i)) <;> rcases j with (j|(j|j)) <;>
    simp_all [normalizedMatrixWire,normalizedSignalWire,controlWire,
      preparationWire,prepGraphWire,filterQspWire,correctionQspWire,PolynomialTransform.flagWire]

def normalizedVectorWire (a n ℓ : ℕ) : Unit ⊕ Fin n → FullWire a n ℓ
  | .inl _ => controlWire a n ℓ .preparation
  | .inr i => .inr i

theorem normalizedVectorWire_injective (a n ℓ : ℕ) : Function.Injective (normalizedVectorWire a n ℓ) := by
  intro i j hij
  rcases i with (i|i) <;> rcases j with (j|j) <;>
    simp_all [normalizedVectorWire,controlWire]




/-- Pure relabeling of matrix indices preserves the same control and argument wires. -/
def LiteralQueryPlacement.reindex {A P Q V W : Type}
    [Fintype A] [DecidableEq A] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
    {arguments : A ≃ (V → Bool)} {coordinates : P → W → Bool} {p : QueryPort A P}
    (L : LiteralQueryPlacement arguments coordinates p) (e : P ≃ Q) :
    LiteralQueryPlacement arguments (fun x=>coordinates (e.symm x)) (Repetition.reindexPort e p) where
  frame := {
    Rest := L.frame.Rest
    finiteRest := L.frame.finiteRest
    decidableRest := L.frame.decidableRest
    wiring := L.frame.wiring.trans e
    correct := by
      intro U
      rw [Repetition.reindexPort_apply,L.frame.correct]
      apply Subtype.ext
      rfl }
  wires := {
    wire := L.wires.wire
    read := by intro x r i; simpa using L.wires.read x r i
    outside := by intro x y r j hj; simpa using L.wires.outside x y r j hj }

/-- A fixed permutation of physical wire names inserts no operation. -/
def LiteralQueryPlacement.wire_equiv {A P V W W' : Type}
    [Fintype A] [DecidableEq A] [Fintype P] [DecidableEq P]
    {arguments : A ≃ (V → Bool)} {coordinates : P → W → Bool}
    {coordinates' : P → W' → Bool} {p : QueryPort A P}
    (L : LiteralQueryPlacement arguments coordinates p) (e : W ≃ W')
    (he : ∀ x i,coordinates' x (e i)=coordinates x i) :
    LiteralQueryPlacement arguments coordinates' p where
  frame := L.frame
  wires := {
    wire := L.wires.wire.trans e.toEmbedding
    read := by
      intro x r i
      rw [show (L.wires.wire.trans e.toEmbedding) i=e (L.wires.wire i) from rfl,he]
      exact L.wires.read x r i
    outside := by
      intro x y r j hj
      obtain ⟨j,rfl⟩ := e.surjective j
      rw [he,he]
      apply L.wires.outside x y r j
      intro i hi
      exact hj i (congrArg e hi) }

/-- Source-coordinate transport preserves the original oracle, including adjoints. -/
def LiteralQueryPlacement.argument_equiv {A B P V W : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype P] [DecidableEq P]
    {arguments : A ≃ (V → Bool)} {coordinates : P → W → Bool} {p : QueryPort A P}
    (L : LiteralQueryPlacement arguments coordinates p) (e : A ≃ B) :
    LiteralQueryPlacement (e.symm.trans arguments) coordinates (OracleCoordinates.port e p) where
  frame := L.frame.coordinates e
  wires := {
    wire := L.wires.wire
    read := by intro x r i; exact L.wires.read (x.1,e.symm x.2) r i
    outside := by intro x y r j hj; exact L.wires.outside (x.1,e.symm x.2) (y.1,e.symm y.2) r j hj }

macro "query_wire" : tactic => `(tactic| simp [registerBits, adapterCoordinates, registerCoordinates, splitRegister, auxCoordinates,
      qCoordinates, prepCoordinates, coarseCoordinates, graphSignalCoordinates, productBits,
      boolCoordinates, phaseBits, matrixArguments, preparationGraphFrame, preparationOracleFrame,
      filterGraphFrame, correctionOracleFrame, tensorFrame, CompilerAttachment.graphFrame,
      CompilerAttachment.vectorFrame, CompilerAttachment.sourceDataFrame,
      PhysicalProgram.preparationFrame, PhysicalProgram.preparationCoordinates,
      preparationRunWiring, coarseWiring, filterWiring, correctionWiring,
      CompilerAttachment.scratchFrame, CompilerAttachment.labelDataFrame, graphLocalWiring,
      graphAttachWiring, oracleAttachWiring, oracleLocalWiring, maskedPhysicalWiring,
      maskSignalEquiv, physicalEquiv, physicalSignalEquiv, graphSignalBits, bitPrefixEquiv,
      normalizedMatrixWire, normalizedSignalWire, normalizedVectorWire, controlWire,
      prepGraphWire, preparationWire, filterQspWire, correctionQspWire,
      Equiv.funSplitAt_symm_apply, GraphEncoding.flagWire, PolynomialTransform.flagWire,
      smallTarget, phaseCoordinates] <;> try rfl)

end OptimalQLS.Refinement.CostedExecution
