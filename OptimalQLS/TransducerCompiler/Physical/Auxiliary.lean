import OptimalQLS.TransducerCompiler.Physical.Work
import OptimalQLS.Refinement.CostedExecution.RealLocality

/-! Literal real auxiliary and clock leaves on the generic physical workspace. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.TransducerCompiler.Physical
open Matrix BinaryClock PolynomialTransform DirtyAncilla
open Refinement.CostedExecution

def auxFrame (m ℓ : ℕ) : GateSynthesis.Space (LabelWire ℓ) × (Bits m × PhaseScratch) ≃ Space m ℓ :=
  tensorFrame (synthWiring (n := Bits m)) (Equiv.refl _)

def labelIndex : Fin 2 ≃ (Unit ⊕ Unit) where
  toFun i := if i=0 then .inl () else .inr ()
  invFun | .inl _ => 0 | .inr _ => 1
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by rcases i with i|i <;> cases i <;> rfl

def auxWireFun (m ℓ : ℕ) : (Unit ⊕ LabelWire ℓ) → Wire m ℓ
  | .inl _ => .inl (.inl ())
  | .inr (.inl i) => .inl (.inr (.inl (.inr (labelIndex i))))
  | .inr (.inr i) => .inl (.inr (.inr i))

def auxSelect (m ℓ : ℕ) : Wire m ℓ → Option (Unit ⊕ LabelWire ℓ)
  | .inl (.inl _) => some (.inl ())
  | .inl (.inr (.inl (.inl _))) => none
  | .inl (.inr (.inl (.inr i))) => some (.inr (.inl (labelIndex.symm i)))
  | .inl (.inr (.inr i)) => some (.inr (.inr i))
  | .inr _ => none

theorem auxSelect_wire (m ℓ : ℕ) (i : Unit ⊕ LabelWire ℓ) :
    auxSelect m ℓ (auxWireFun m ℓ i)=some i := by
  rcases i with i|(i|i)
  · cases i; rfl
  · simp [auxSelect,auxWireFun]
  · rfl

def auxWire (m ℓ : ℕ) : (Unit ⊕ LabelWire ℓ) ↪ Wire m ℓ where
  toFun := auxWireFun m ℓ
  inj' := by
    intro i j he
    have hh := congrArg (auxSelect m ℓ) he
    simpa only [auxSelect_wire,Option.some.injEq] using hh

def auxEmbedding (m ℓ : ℕ) :
    WireEmbedding phaseBits (coordinates m ℓ) (auxFrame m ℓ) where
  wire := auxWire m ℓ
  read := by
    intro x r i
    rcases i with i|(i|i)
    · rfl
    · fin_cases i
      · change (labelBitsEquiv (labelBitsEquiv.symm (x.2 (.inl 0),x.2 (.inl 1)))).1=x.2 (.inl 0)
        rw [Equiv.apply_symm_apply]
      · change (labelBitsEquiv (labelBitsEquiv.symm (x.2 (.inl 0),x.2 (.inl 1)))).2=x.2 (.inl 1)
        rw [Equiv.apply_symm_apply]
    · cases i <;> rfl
  outside := by
    intro x y r j hj
    rcases j with (j|((j|j)|j))|j
    · cases j; exact False.elim (hj (.inl ()) rfl)
    · rfl
    · have he : auxWire m ℓ (.inr (.inl (labelIndex.symm j)))=.inl (.inr (.inl (.inr j))) := by
        simp [auxWire,auxWireFun]
      exact False.elim (hj _ he)
    · exact False.elim (hj (.inr (.inr j)) rfl)
    · rfl

def auxGateEval (m ℓ : ℕ) (g : PhaseGate (LabelWire ℓ)) : Matrix.unitaryGroup (Space m ℓ) ℂ :=
  GateSynthesis.placeHom (auxFrame m ℓ) g.eval

theorem aux_gate_local (m ℓ : ℕ) (g : PhaseGate (LabelWire ℓ)) :
    IsTwoLocal (coordinates m ℓ) (auxGateEval m ℓ g) :=
  IsTwoLocal.place _ (auxEmbedding m ℓ) _ (phase_leaf_local g)

theorem aux_placement (m ℓ : ℕ) (U : Matrix.unitaryGroup (GateSynthesis.Space (LabelWire ℓ)) ℂ) :
    GateSynthesis.placeHom (auxFrame m ℓ) U=padded m ℓ (lowerAuxHom U) := by
  unfold auxFrame padded lowerAuxHom
  rw [placeHom_comp]

def auxCode (m ℓ : ℕ) (p : List (PhaseGate (LabelWire ℓ))) :
    NamedCircuit (PhaseGate (LabelWire ℓ)) (Bits m) (Bits m) (Space m ℓ) := p.map .gate

theorem auxCode_counts (m ℓ : ℕ) (p : List (PhaseGate (LabelWire ℓ))) :
    ((auxCode m ℓ p).toQuery (auxGateEval m ℓ)).matrixQueries=0 ∧
    ((auxCode m ℓ p).toQuery (auxGateEval m ℓ)).vectorQueries=0 ∧
    (auxCode m ℓ p).workGates=p.length := by
  induction p with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons g p ih => exact ⟨ih.1,ih.2.1,congrArg Nat.succ ih.2.2⟩

theorem auxCode_eval (m ℓ : ℕ) (p : List (PhaseGate (LabelWire ℓ)))
    (U₁ U₂ : Matrix.unitaryGroup (Bits m) ℂ) :
    ((auxCode m ℓ p).toQuery (auxGateEval m ℓ)).eval U₁ U₂=
      GateSynthesis.placeHom (auxFrame m ℓ) (phaseEval p) := by
  induction p with
  | nil => simp [auxCode,NamedCircuit.toQuery,QueryCircuit.eval,phaseEval]
  | cons g p ih =>
    simp only [auxCode,List.map_cons,NamedCircuit.toQuery,NamedInstruction.toQuery,
      QueryCircuit.eval,QueryInstruction.eval,phaseEval,map_mul]
    exact congrArg (fun U=>U*auxGateEval m ℓ g) ih

theorem auxCode_intertwines (m ℓ : ℕ) (p : List (PhaseGate (LabelWire ℓ)))
    (U₁ U₂ : Matrix.unitaryGroup (Bits m) ℂ) :
    (((auxCode m ℓ p).toQuery (auxGateEval m ℓ)).eval U₁ U₂).val*basisInsertion (clean m ℓ)=
      basisInsertion (clean m ℓ)*(lowerAuxHom (phaseEval p)).val := by
  rw [auxCode_eval,aux_placement,padded_clean]

theorem clock_intertwines (m ℓ : ℕ) (adj : Bool)
    (S : Matrix.unitaryGroup (Base (Bits m)) ℂ) (U₁ U₂ : Matrix.unitaryGroup (Bits m) ℂ) :
    (((auxCode m ℓ (Preparation.CompilerAttachment.ClockGates.labelCode ℓ)).toQuery
      (auxGateEval m ℓ)).eval U₁ U₂).val*basisInsertion (clean m ℓ)=
      basisInsertion (clean m ℓ)*((SynthInstruction.clock adj).eval S U₁ U₂).val := by
  rw [auxCode_intertwines,Preparation.CompilerAttachment.ClockGates.labelCode_synth_eval ℓ S U₁ U₂ adj]

end OptimalQLS.TransducerCompiler.Physical
