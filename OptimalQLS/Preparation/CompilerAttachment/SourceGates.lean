import OptimalQLS.Preparation.CompilerAttachment.SourceFrames

/-! # Strictly singly-controlled original source queries and source-basis phases -/
noncomputable section
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 150000
set_option maxRecDepth 2048
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.Preparation.CompilerAttachment
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla

inductive SourceGate (n : ℕ) where
  | oracle (g : PhaseGate OracleLocalWire)
  | phase (g : PhaseGate (ReflectionWire n))

def sourceGateEval (a n ℓ : ℕ) : SourceGate n → Matrix.unitaryGroup (Physical a n ℓ) ℂ
  | .oracle g => GateSynthesis.placeHom (vectorFrame a n ℓ) (elementaryPlacement g.eval)
  | .phase g => GateSynthesis.placeHom (reflectionFrame a n ℓ) g.eval

def SourceGate.arity {n : ℕ} : SourceGate n → ℕ
  | .oracle g => g.arity
  | .phase g => g.arity

theorem SourceGate.arity_le_two {n : ℕ} (g : SourceGate n) : g.arity≤2 := by
  cases g <;> exact PhaseGate.arity_le_two _

abbrev SourceCircuit (a n ℓ : ℕ) :=
  NamedCircuit (SourceGate n) (Bits a × Bits n) (Bits n) (Physical a n ℓ)

def sourceCall (a n ℓ : ℕ) (l : Label) (adj : Bool) : SourceCircuit a n ℓ :=
  attachList (vectorFrame a n ℓ) SourceGate.oracle
    (swapElementary (localOracleCode (A := Bits n) (B := Bits a × Bits n) (labelBitsEquiv l) adj))

def sourceSingleFlagPort (a n ℓ : ℕ) : QueryPort (Bits n) (Physical a n ℓ) :=
  (scratchPort (vectorFrame a n ℓ)).comp
    (GraphEncoding.singleFlagOraclePort (Bits n) (smallTarget 2))


theorem sourceCall_counts (a n ℓ : ℕ) (l : Label) (adj : Bool) :
    ((sourceCall a n ℓ l adj).toQuery (sourceGateEval a n ℓ)).matrixQueries=0 ∧
      ((sourceCall a n ℓ l adj).toQuery (sourceGateEval a n ℓ)).vectorQueries=1 ∧
      (sourceCall a n ℓ l adj).workGates≤2400 := by
  have hc := localOracleCode_counts (A := Bits n) (B := Bits a × Bits n) (labelBitsEquiv l) adj
  simp only [sourceCall,attachList_toQuery (vectorFrame a n ℓ) SourceGate.oracle (sourceGateEval a n ℓ)
    (fun _=>rfl),swapElementary_toQuery,(QueryCircuit.lift_counts _ _).1,
    (QueryCircuit.lift_counts _ _).2,(QueryCircuit.swapOracles_counts _).1,
    (QueryCircuit.swapOracles_counts _).2,attachList_workGates,swapElementary_workGates]
  exact ⟨hc.2.1,hc.1,hc.2.2⟩


theorem sourceCall_eval (a n ℓ : ℕ) (l : Label) (adj : Bool)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    ((sourceCall a n ℓ l adj).toQuery (sourceGateEval a n ℓ)).eval UA Ub=
      GateSynthesis.placeHom (vectorFrame a n ℓ)
        ((localOracleCode (labelBitsEquiv l) adj).toQuery.eval Ub UA) := by
  rw [sourceCall,attachList_eval (vectorFrame a n ℓ) SourceGate.oracle (sourceGateEval a n ℓ)
    (fun _=>rfl),swapElementary_toQuery,QueryCircuit.swapOracles_eval]


theorem sourceCall_intertwines (a n ℓ : ℕ) (l : Label) (adj : Bool)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    (((sourceCall a n ℓ l adj).toQuery (sourceGateEval a n ℓ)).eval UA Ub).val *
        basisInsertion (clean a n ℓ)=
      basisInsertion (clean a n ℓ)*
        (GateSynthesis.placeHom (sourceDataFrame a n ℓ)
          ((GraphEncoding.maskedGraphPort (Bits n) (labelBitsEquiv l)).apply
            (if adj then Ub⁻¹ else Ub))).val := by
  rw [sourceCall_eval]
  exact vectorFrame_intertwines a n ℓ _ _ (localOracleCode_intertwines (labelBitsEquiv l) adj Ub UA)


theorem sourceCall_single_flag (a n ℓ : ℕ) (l : Label) (adj : Bool)
    (p : QueryPort (Bits n) (Physical a n ℓ)) (b : Bool)
    (hp : NamedInstruction.vectorCall p b ∈ sourceCall a n ℓ l adj) :
    p=sourceSingleFlagPort a n ℓ ∧ b=adj := by
  obtain ⟨i,hi,hEq⟩ := List.mem_map.mp hp
  obtain ⟨j,hj,hji⟩ := List.mem_map.mp hi
  cases j with
  | gate g => cases hji; cases hEq
  | matrixCall q d =>
    cases hji
    have hq := GraphEncoding.maskedOracleCircuit_single_flag 2 id Function.injective_id
      ![(labelBitsEquiv l).1,(labelBitsEquiv l).2] adj q d hj
    rcases hq with ⟨rfl,rfl⟩
    cases hEq
    exact ⟨rfl,rfl⟩
  | vectorCall q d => cases hji; cases hEq


def sourcePhaseMacro (a n ℓ : ℕ) (code : List (PhaseGate (ReflectionWire n))) : SourceCircuit a n ℓ :=
  code.map (fun g=>.gate (.phase g))

def reflectionMacro (a n ℓ : ℕ) : SourceCircuit a n ℓ :=
  sourcePhaseMacro a n ℓ (reflectionPhaseCode n)

theorem sourcePhaseMacro_counts (a n ℓ : ℕ) (c : List (PhaseGate (ReflectionWire n))) :
    ((sourcePhaseMacro a n ℓ c).toQuery (sourceGateEval a n ℓ)).matrixQueries=0 ∧
    ((sourcePhaseMacro a n ℓ c).toQuery (sourceGateEval a n ℓ)).vectorQueries=0 ∧
    (sourcePhaseMacro a n ℓ c).workGates=c.length := by
  induction c with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons g c ih =>
    exact ⟨ih.1,ih.2.1,congrArg Nat.succ ih.2.2⟩

theorem reflectionMacro_counts (a n ℓ : ℕ) :
    ((reflectionMacro a n ℓ).toQuery (sourceGateEval a n ℓ)).matrixQueries=0 ∧
      ((reflectionMacro a n ℓ).toQuery (sourceGateEval a n ℓ)).vectorQueries=0 ∧
      (reflectionMacro a n ℓ).workGates≤6422*(n+1) := by
  have h := sourcePhaseMacro_counts a n ℓ (reflectionPhaseCode n)
  exact ⟨h.1,h.2.1,h.2.2.le.trans (reflectionPhaseCode_length n)⟩

theorem sourcePhaseMacro_eval (a n ℓ : ℕ) (c : List (PhaseGate (ReflectionWire n)))
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    ((sourcePhaseMacro a n ℓ c).toQuery (sourceGateEval a n ℓ)).eval UA Ub=
      GateSynthesis.placeHom (reflectionFrame a n ℓ) (phaseEval c) := by
  induction c with
  | nil => simp [sourcePhaseMacro,NamedCircuit.toQuery,QueryCircuit.eval,phaseEval]
  | cons g c ih =>
    simp only [sourcePhaseMacro,List.map_cons,NamedCircuit.toQuery,NamedInstruction.toQuery,
      QueryCircuit.eval,QueryInstruction.eval,phaseEval,map_mul]
    exact congrArg (fun U=>U * GateSynthesis.placeHom (reflectionFrame a n ℓ) g.eval) ih

theorem reflectionMacro_eval (a n ℓ : ℕ)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    ((reflectionMacro a n ℓ).toQuery (sourceGateEval a n ℓ)).eval UA Ub=
      GateSynthesis.placeHom (reflectionFrame a n ℓ) (phaseEval (reflectionPhaseCode n)) :=
  sourcePhaseMacro_eval a n ℓ _ UA Ub

theorem reflectionMacro_intertwines (a n ℓ : ℕ)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    (((reflectionMacro a n ℓ).toQuery (sourceGateEval a n ℓ)).eval UA Ub).val *
        basisInsertion (clean a n ℓ)=
      basisInsertion (clean a n ℓ)*
        (GateSynthesis.placeHom (reflectionSourceFrame a n ℓ) (reflectionPhaseUnitary n)).val := by
  rw [reflectionMacro_eval]
  exact reflectionFrame_intertwines a n ℓ

end OptimalQLS.Preparation.CompilerAttachment
