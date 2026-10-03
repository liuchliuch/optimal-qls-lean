import OptimalQLS.Reduction.PhysicalAdapter.Substitution

/-! Gate and actual original-query provenance on the substituted list. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.Reduction.PhysicalAdapter
open Matrix PolynomialTransform TransducerCompiler BinaryClock Refinement.PhysicalProgram DirtyAncilla

def originalMatrixPort (a n ℓ : ℕ) (f : Flag) : QueryPort (Bits a × Bits n) (Space a n ℓ) :=
  (scratchPort (matrixWiring a n ℓ f)).comp
    (GraphEncoding.singleFlagOraclePort (Bits a × Bits n) (smallTarget 2))

def originalVectorPort (a n ℓ : ℕ) : QueryPort (Bits n) (Space a n ℓ) :=
  (scratchPort (vectorWiring a n ℓ)).comp
    (GraphEncoding.singleFlagOraclePort (Bits n) (.inl 0 : DilationWire))

def Gate.RealAddition {a n ℓ : ℕ} : Gate a n ℓ → Prop
  | .old _ => True
  | .matrix _ g => GraphEncoding.RealPhaseGate g
  | .vector _ => False

def Safe {a n ℓ : ℕ} (c : Circuit a n ℓ) : Prop :=
  (∀ g,NamedInstruction.gate g∈c → g.RealAddition ∧ g.arity≤2) ∧
  (∀ p adj,NamedInstruction.matrixCall p adj∈c → ∃ f,p=originalMatrixPort a n ℓ f) ∧
  (∀ p adj,NamedInstruction.vectorCall p adj∈c → p=originalVectorPort a n ℓ)

theorem matrixCode_safe (a n ℓ : ℕ) (hℓ : 0<ℓ) (f : Flag) (adj : Bool) :
    Safe (matrixCode a n ℓ f adj) := by
  constructor
  · intro g hg
    obtain ⟨i,hi,he⟩ := List.mem_map.mp hg
    cases i with
    | gate g =>
      cases he
      exact dilationOracleCircuit_real adj g hi
    | matrixCall p adj => cases he
    | vectorCall p adj => cases he
  constructor
  · intro p adj hp
    obtain ⟨i,hi,he⟩ := List.mem_map.mp hp
    cases i with
    | gate g => cases he
    | matrixCall q b =>
      cases he
      refine ⟨f,?_⟩
      rw [dilationOracleCircuit_single_flag _ q _ hi]
      rfl
    | vectorCall q b => cases he
  · intro p adj hp
    exact False.elim (Preparation.CompilerAttachment.named_no_vector _ _
      (matrixCode_counts a n ℓ hℓ f _).2.1 p adj hp)

theorem vectorCode_safe (a n ℓ : ℕ) (adj : Bool) : Safe (vectorCode a n ℓ adj) := by
  constructor
  · intro g hg
    simp [vectorCode,vectorDilationCircuit,Preparation.CompilerAttachment.attachList,
      Preparation.CompilerAttachment.attachInstruction] at hg
  constructor
  · intro p b hp
    simp [vectorCode,vectorDilationCircuit,Preparation.CompilerAttachment.attachList,
      Preparation.CompilerAttachment.attachInstruction] at hp
  · intro p b hp
    simp only [vectorCode,vectorDilationCircuit,Preparation.CompilerAttachment.attachList,
      List.map_cons,List.map_nil,Preparation.CompilerAttachment.attachInstruction,List.mem_singleton] at hp
    cases hp
    rfl

theorem substitute_safe (a n ℓ : ℕ) (hℓ : 0<ℓ)
    (c : Refinement.PhysicalProgram.Circuit a (n+1) ℓ) : Safe (substitute a n ℓ c) := by
  have hi (i : NamedInstruction (Refinement.PhysicalProgram.Gate a (n+1) ℓ)
      (Bits a × Bits (n+1)) (Bits (n+1)) (Register a (n+1) ℓ)) :
      Safe (substituteInstruction a n ℓ i) := by
    cases i with
    | gate g =>
      refine ⟨?_,?_,?_⟩
      · intro q hq
        have hq' : q=Gate.old g := by simpa [substituteInstruction] using hq
        subst q
        exact ⟨True.intro,Gate.arity_le_two _⟩
      · intro p b hp; simp [substituteInstruction] at hp
      · intro p b hp; simp [substituteInstruction] at hp
    | matrixCall p b => exact matrixCode_safe a n ℓ hℓ _ b
    | vectorCall p b => exact vectorCode_safe a n ℓ b
  refine ⟨?_,?_,?_⟩
  · intro g hg
    obtain ⟨i,_,hg⟩ := List.mem_flatMap.mp hg
    exact (hi i).1 g hg
  · intro p b hp
    obtain ⟨i,_,hp⟩ := List.mem_flatMap.mp hp
    exact (hi i).2.1 p b hp
  · intro p b hp
    obtain ⟨i,_,hp⟩ := List.mem_flatMap.mp hp
    exact (hi i).2.2 p b hp

/-- Local macro coordinates read one literal qubit, through a displayed wire regrouping. -/
def matrixFlag (a n ℓ : ℕ) (f : Flag) (x : Space a n ℓ) : Bool :=
  ((matrixWiring a n ℓ f).symm x).1.1.2 (smallTarget 2)

def vectorFlag (a n ℓ : ℕ) (x : Space a n ℓ) : Bool :=
  ((vectorWiring a n ℓ).symm x).1.1.2 (.inl 0)

theorem singleFlagPort_reads {A ι : Type} [Fintype A] [DecidableEq A]
    [Fintype ι] [DecidableEq ι] (t : ι) :
    ReadsFlag (GraphEncoding.singleFlagOraclePort A t) (fun x=>x.1.2 t) := by
  intro i k
  simp [GraphEncoding.singleFlagOraclePort]

theorem originalMatrixPort_reads (a n ℓ : ℕ) (f : Flag) :
    ReadsFlag (originalMatrixPort a n ℓ f) (matrixFlag a n ℓ f) := by
  apply readsFlag_lift _ _ (fun x=>x.1.2 (smallTarget 2)) _ (fun _=>rfl)
  · intro i k
    simp [matrixFlag,scratchPort]
  · exact singleFlagPort_reads _

theorem originalVectorPort_reads (a n ℓ : ℕ) :
    ReadsFlag (originalVectorPort a n ℓ) (vectorFlag a n ℓ) := by
  apply readsFlag_lift _ _ (fun x=>x.1.2 (.inl 0 : DilationWire)) _ (fun _=>rfl)
  · intro i k
    simp [vectorFlag,scratchPort]
  · exact singleFlagPort_reads _

/-- All three matrix placements query the very same fresh scratch flag. -/
theorem matrixFlag_shared (a n ℓ : ℕ) (f : Flag) (x : Space a n ℓ) :
    matrixFlag a n ℓ f x=x.2.2.1 := by
  simp [matrixFlag,matrixWiring,Preparation.CompilerAttachment.scratchFrame,
    dilationFull,oracleLocalWiring,smallTarget]

end OptimalQLS.Reduction.PhysicalAdapter
