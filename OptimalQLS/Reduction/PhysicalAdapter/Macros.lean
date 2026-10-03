import OptimalQLS.Reduction.PhysicalAdapter.Placement

/-! Actual original-oracle macros, including the unchanged old work leaves. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.Reduction.PhysicalAdapter
open Matrix PolynomialTransform TransducerCompiler BinaryClock Refinement.PhysicalProgram DirtyAncilla LowerBounds

inductive Gate (a n ℓ : ℕ) where
  | old (g : Refinement.PhysicalProgram.Gate a (n+1) ℓ)
  | matrix (f : Flag) (g : PhaseGate DilationWire)
  | vector (g : PhaseGate DilationWire)

def Gate.arity {a n ℓ : ℕ} : Gate a n ℓ → ℕ
  | .old g => g.arity
  | .matrix _ g => g.arity
  | .vector g => g.arity

def gateEval (a n ℓ : ℕ) (hℓ : 0<ℓ) : Gate a n ℓ → Matrix.unitaryGroup (Space a n ℓ) ℂ
  | .old g => (scratchPort (Equiv.refl _)).apply (Refinement.PhysicalProgram.gateEval a (n+1) ℓ hℓ g)
  | .matrix f g => GateSynthesis.placeHom (matrixWiring a n ℓ f) (elementaryPlacement g.eval)
  | .vector g => GateSynthesis.placeHom (vectorWiring a n ℓ) (elementaryPlacement g.eval)

theorem Gate.arity_le_two {a n ℓ : ℕ} (g : Gate a n ℓ) : g.arity≤2 := by
  cases g with
  | old g => exact Refinement.PhysicalProgram.Gate.arity_le_two g
  | matrix f g => exact PhaseGate.arity_le_two g
  | vector g => exact PhaseGate.arity_le_two g

abbrev Circuit (a n ℓ : ℕ) :=
  NamedCircuit (Gate a n ℓ) (Bits a × Bits n) (Bits n) (Space a n ℓ)

def matrixCode (a n ℓ : ℕ) (f : Flag) (adj : Bool) : Circuit a n ℓ :=
  Preparation.CompilerAttachment.attachList (matrixWiring a n ℓ f) (Gate.matrix f)
    (dilationOracleCircuit adj)

def vectorCode (a n ℓ : ℕ) (adj : Bool) : Circuit a n ℓ :=
  Preparation.CompilerAttachment.attachList (vectorWiring a n ℓ) Gate.vector (vectorDilationCircuit adj)

def matrixOracle {a n : ℕ} (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) :
    Matrix.unitaryGroup (Bits a × Bits (n+1)) ℂ :=
  rewireUnitary (matrixCoordinates a n).symm (dilationEncoding UA)

def vectorOracle {n : ℕ} (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    Matrix.unitaryGroup (Bits (n+1)) ℂ :=
  rewireUnitary (sumBits n).symm (preparation Ub)

theorem matrixCode_counts (a n ℓ : ℕ) (hℓ : 0<ℓ) (f : Flag) (adj : Bool) :
    ((matrixCode a n ℓ f adj).toQuery (gateEval a n ℓ hℓ)).matrixQueries=2 ∧
      ((matrixCode a n ℓ f adj).toQuery (gateEval a n ℓ hℓ)).vectorQueries=0 ∧
      (matrixCode a n ℓ f adj).workGates≤4801 := by
  rw [matrixCode,Preparation.CompilerAttachment.attachList_toQuery
    (matrixWiring a n ℓ f) (Gate.matrix f) (gateEval a n ℓ hℓ) (fun _=>rfl)]
  exact ⟨(QueryCircuit.lift_counts _ _).1.trans (dilationOracleCircuit_counts adj).1,
    (QueryCircuit.lift_counts _ _).2.trans (dilationOracleCircuit_counts adj).2.1,
    by rw [Preparation.CompilerAttachment.attachList_workGates]; exact (dilationOracleCircuit_counts adj).2.2⟩

theorem vectorCode_counts (a n ℓ : ℕ) (hℓ : 0<ℓ) (adj : Bool) :
    ((vectorCode a n ℓ adj).toQuery (gateEval a n ℓ hℓ)).matrixQueries=0 ∧
      ((vectorCode a n ℓ adj).toQuery (gateEval a n ℓ hℓ)).vectorQueries=1 ∧
      (vectorCode a n ℓ adj).workGates=0 := by
  rw [vectorCode,Preparation.CompilerAttachment.attachList_toQuery
    (vectorWiring a n ℓ) Gate.vector (gateEval a n ℓ hℓ) (fun _=>rfl)]
  exact ⟨(QueryCircuit.lift_counts _ _).1.trans (vectorDilationCircuit_counts adj).1,
    (QueryCircuit.lift_counts _ _).2.trans (vectorDilationCircuit_counts adj).2.1,
    by rw [Preparation.CompilerAttachment.attachList_workGates]; exact (vectorDilationCircuit_counts adj).2.2⟩

theorem matrixCode_intertwines (a n ℓ : ℕ) (hℓ : 0<ℓ) (f : Flag) (adj : Bool)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    (((matrixCode a n ℓ f adj).toQuery (gateEval a n ℓ hℓ)).eval UA Ub).val *
      basisInsertion (clean a n ℓ)=basisInsertion (clean a n ℓ)*
        ((matrixPort a (n+1) ℓ f).apply (if adj then (matrixOracle UA)⁻¹ else matrixOracle UA)).val := by
  rw [matrixCode,Preparation.CompilerAttachment.attachList_eval
    (matrixWiring a n ℓ f) (Gate.matrix f) (gateEval a n ℓ hℓ) (fun _=>rfl)]
  have ht := tensor_intertwines (D := (matrixFrame a n ℓ f).Rest) dilationSignalClean _ _
    (dilationEncodingCircuit_intertwines adj UA Ub)
  have he := clean_intertwines_transport (matrixWiring a n ℓ f) (matrixFrame a n ℓ f).wiring
    (fun x=>(dilationSignalClean x.1,x.2)) _ _ ht
  have hc : (fun x => matrixWiring a n ℓ f
      (dilationSignalClean (((matrixFrame a n ℓ f).wiring.symm x).1),
        ((matrixFrame a n ℓ f).wiring.symm x).2))=clean a n ℓ := by
    funext x
    rw [matrixWiring_clean,Equiv.apply_symm_apply]
  rw [hc] at he
  have hp := (matrixFrame a n ℓ f).correct (if adj then (dilationEncoding UA)⁻¹ else dilationEncoding UA)
  rw [OracleCoordinates.port_apply_adjoint] at hp
  simp only [matrixOracle,vectorOracle]
  rw [hp]
  exact he

theorem vectorCode_intertwines (a n ℓ : ℕ) (hℓ : 0<ℓ) (adj : Bool)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    (((vectorCode a n ℓ adj).toQuery (gateEval a n ℓ hℓ)).eval UA Ub).val *
      basisInsertion (clean a n ℓ)=basisInsertion (clean a n ℓ)*
        ((preparationVectorPort a (n+1) ℓ).apply (if adj then (vectorOracle Ub)⁻¹ else vectorOracle Ub)).val := by
  rw [vectorCode,Preparation.CompilerAttachment.attachList_eval
    (vectorWiring a n ℓ) Gate.vector (gateEval a n ℓ hℓ) (fun _=>rfl)]
  have ht := tensor_intertwines (D := (vectorFrame a n ℓ).Rest) dilationSumClean _ _
    (preparationCircuit_intertwines adj UA Ub)
  have he := clean_intertwines_transport (vectorWiring a n ℓ) (vectorFrame a n ℓ).wiring
    (fun x=>(dilationSumClean x.1,x.2)) _ _ ht
  have hc : (fun x => vectorWiring a n ℓ
      (dilationSumClean (((vectorFrame a n ℓ).wiring.symm x).1),
        ((vectorFrame a n ℓ).wiring.symm x).2))=clean a n ℓ := by
    funext x
    rw [vectorWiring_clean,Equiv.apply_symm_apply]
  rw [hc] at he
  have hp := (vectorFrame a n ℓ).correct (if adj then (preparation Ub)⁻¹ else preparation Ub)
  rw [OracleCoordinates.port_apply_adjoint] at hp
  simp only [matrixOracle,vectorOracle]
  rw [hp]
  exact he

end OptimalQLS.Reduction.PhysicalAdapter
