import OptimalQLS.Reduction.GenericSolver.PhysicalSubstitution
import OptimalQLS.Refinement.CostedExecution.AdapterQueryLocalityFilterDirectCore

/-! Every emitted query is a literal original-oracle argument register plus
one control bit. Every added gate is a real, semantically at-most-two-bit gate. -/
noncomputable section
open scoped Classical
namespace OptimalQLS.Reduction.GenericSolver.Physical
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
open Refinement.CostedExecution Refinement.PhysicalMeasurement Preparation.CompilerAttachment
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
variable {P W : Type} [Fintype P] [DecidableEq P]
  {chart : P ≃ (W → Bool)} {a n : ℕ}

def originalMatrixPort (F : MatrixFrame chart a n) : QueryPort (Bits a × Bits n) (P × PhaseScratch) :=
  (scratchPort (matrixWiring a n F.frame)).comp
    (GraphEncoding.singleFlagOraclePort (Bits a × Bits n) (smallTarget 2))
def originalVectorPort (F : VectorFrame chart n) : QueryPort (Bits n) (P × PhaseScratch) :=
  (scratchPort (vectorWiring n F.frame)).comp
    (GraphEncoding.singleFlagOraclePort (Bits n) (.inl 0 : DilationWire))

def localFlagEmbedding {Q V : Type} [Fintype Q] [DecidableEq Q]
    (arguments : Q ≃ (V → Bool)) (t : DilationWire) :
    WireEmbedding (productBits boolCoordinates arguments)
      (productBits (phaseCoordinates DilationWire) arguments) (PhysicalAdapter.flagFrame t Q) where
  wire := ⟨fun i=>match i with
    | .inl _ => .inl (.inr t)
    | .inr i => .inr i,by intro i j he; cases i <;> cases j <;> simp_all⟩
  read := by
    intro x r i
    cases i with
    | inl i => cases i; simp [PhysicalAdapter.flagFrame,phaseCoordinates,productBits,
        boolCoordinates,Equiv.funSplitAt_symm_apply]
    | inr i => rfl
  outside := by
    intro x y r j hj
    rcases j with (j|j)|j
    · rfl
    · have hn : j≠t := by intro he; subst j; exact hj (.inl ()) rfl
      simp [PhysicalAdapter.flagFrame,phaseCoordinates,productBits,
        Equiv.funSplitAt_symm_apply,hn]
    · exact False.elim (hj (.inr j) rfl)

def matrixPlacement (F : MatrixFrame chart a n) :
    LiteralQueryPlacement (matrixArguments a n) (coordinates chart) (originalMatrixPort F) where
  frame := ControlFrame.direct_lift (PhysicalAdapter.singleFlagFrame (smallTarget 2))
    (matrixWiring a n F.frame)
  wires := (localFlagEmbedding (matrixArguments a n) (smallTarget 2)).comp F.wires

def vectorPlacement (F : VectorFrame chart n) :
    LiteralQueryPlacement (Equiv.refl (Bits n)) (coordinates chart) (originalVectorPort F) where
  frame := ControlFrame.direct_lift (PhysicalAdapter.singleFlagFrame (.inl 0 : DilationWire))
    (vectorWiring n F.frame)
  wires := (localFlagEmbedding (Equiv.refl (Bits n)) (.inl 0)).comp F.wires

def Gate.AddedReal : Gate chart a n → Prop
  | .old _ => True
  | .matrix _ g => GraphEncoding.RealPhaseGate g
  | .vector _ _ => False

def Safe (c : Circuit chart a n) : Prop :=
  (∀ g, NamedInstruction.gate g∈c → g.AddedReal) ∧
  (∀ p adj, NamedInstruction.matrixCall p adj∈c → ∃ F : MatrixFrame chart a n, p=originalMatrixPort F) ∧
  (∀ p adj, NamedInstruction.vectorCall p adj∈c → ∃ F : VectorFrame chart n, p=originalVectorPort F)

theorem matrixCode_safe (F : MatrixFrame chart a n) (adj : Bool) : Safe (matrixCode F adj) := by
  constructor
  · intro g hg
    obtain ⟨i,hi,he⟩ := List.mem_map.mp hg
    cases i with
    | gate g => cases he; exact (dilationOracleCircuit_real adj g hi).1
    | matrixCall p adj => cases he
    | vectorCall p adj => cases he
  constructor
  · intro p adj hp
    obtain ⟨i,hi,he⟩ := List.mem_map.mp hp
    cases i with
    | gate g => cases he
    | matrixCall q b =>
      cases he
      refine ⟨F,?_⟩
      rw [dilationOracleCircuit_single_flag _ q _ hi]
      rfl
    | vectorCall q b => cases he
  · intro p adj hp
    exact False.elim (named_no_vector _ _ (matrixCode_counts F _).2.1 p adj hp)

theorem vectorCode_safe (F : VectorFrame chart n) (adj : Bool) : Safe (vectorCode (a := a) F adj) := by
  constructor
  · intro g hg
    simp [vectorCode,vectorDilationCircuit,attachList,attachInstruction] at hg
  constructor
  · intro p b hp
    simp [vectorCode,vectorDilationCircuit,attachList,attachInstruction] at hp
  · intro p b hp
    simp only [vectorCode,vectorDilationCircuit,attachList,List.map_cons,List.map_nil,
      attachInstruction,List.mem_singleton] at hp
    cases hp
    exact ⟨F,rfl⟩

theorem instructionCode_safe (i : SourceInstruction chart a n) : Safe (instructionCode i) := by
  cases i with
  | gate g =>
    refine ⟨?_,?_,?_⟩
    · intro q hq
      have hq' : q=Gate.old g := by simpa [instructionCode] using hq
      subst q
      trivial
    · intro p b hp; simp [instructionCode] at hp
    · intro p b hp; simp [instructionCode] at hp
  | matrix F b => exact matrixCode_safe F b
  | vector F b => exact vectorCode_safe F b

theorem substitute_safe (c : SourceCircuit chart a n) : Safe (substitute c) := by
  refine ⟨?_,?_,?_⟩
  · intro g hg
    obtain ⟨i,_,hg⟩ := List.mem_flatMap.mp hg
    exact (instructionCode_safe i).1 g hg
  · intro p b hp
    obtain ⟨i,_,hp⟩ := List.mem_flatMap.mp hp
    exact (instructionCode_safe i).2.1 p b hp
  · intro p b hp
    obtain ⟨i,_,hp⟩ := List.mem_flatMap.mp hp
    exact (instructionCode_safe i).2.2 p b hp

theorem substitute_matrix_placement (c : SourceCircuit chart a n)
    (p : QueryPort (Bits a × Bits n) (P × PhaseScratch)) (adj : Bool)
    (hp : NamedInstruction.matrixCall p adj∈substitute c) :
    Nonempty (LiteralQueryPlacement (matrixArguments a n) (coordinates chart) p) := by
  obtain ⟨F,rfl⟩ := (substitute_safe c).2.1 p adj hp
  exact ⟨matrixPlacement F⟩

theorem substitute_vector_placement (c : SourceCircuit chart a n)
    (p : QueryPort (Bits n) (P × PhaseScratch)) (adj : Bool)
    (hp : NamedInstruction.vectorCall p adj∈substitute c) :
    Nonempty (LiteralQueryPlacement (Equiv.refl (Bits n)) (coordinates chart) p) := by
  obtain ⟨F,rfl⟩ := (substitute_safe c).2.2 p adj hp
  exact ⟨vectorPlacement F⟩

end OptimalQLS.Reduction.GenericSolver.Physical
