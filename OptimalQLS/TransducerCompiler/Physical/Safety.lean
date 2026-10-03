import OptimalQLS.TransducerCompiler.Physical.Assembly
import OptimalQLS.TransducerCompiler.Physical.QueryLocality
import OptimalQLS.Preparation.CompilerAttachment.GlobalSafety

/-! Semantic locality, real auxiliary leaves and full original-oracle wire placement. -/
noncomputable section
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.TransducerCompiler.Physical
open Matrix BinaryClock PolynomialTransform DirtyAncilla
open Refinement.CostedExecution Preparation.CompilerAttachment

def Gate.AuxiliaryReal {m ℓ : ℕ} : Gate m ℓ → Prop
  | .work _ => True
  | .auxiliary g => GraphEncoding.RealPhaseGate g
  | .query g => GraphEncoding.RealPhaseGate g

theorem gate_local (m ℓ : ℕ) (hℓ : 0<ℓ) (g : Gate m ℓ) :
    IsTwoLocal (coordinates m ℓ) (gateEval m ℓ hℓ g) := by
  cases g with
  | work g => exact placed_work_local m ℓ hℓ g
  | auxiliary g => exact aux_gate_local m ℓ g
  | query g => exact query_gate_local m ℓ g

theorem auxiliary_gate_real (m ℓ : ℕ) (g : PhaseGate (LabelWire ℓ))
    (hg : GraphEncoding.RealPhaseGate g) : ∀ i j, ((auxGateEval m ℓ g).val i j).im=0 :=
  GateSynthesis.placeHom_real _ _ hg

theorem query_gate_real (m ℓ : ℕ) (g : PhaseGate OracleLocalWire)
    (hg : GraphEncoding.RealPhaseGate g) : ∀ i j, ((queryGateEval m ℓ g).val i j).im=0 :=
  GateSynthesis.placeHom_real _ _ (GateSynthesis.placeHom_real _ _ hg)

def localSafe (m : ℕ) : ElementaryInstruction (Bits m) (Bits m) OracleLocalWire (Bits m) → Prop
  | .gate g => GraphEncoding.RealPhaseGate g
  | .matrixCall p _ => p=GraphEncoding.singleFlagOraclePort (Bits m) (smallTarget 2)
  | .vectorCall p _ => p=GraphEncoding.singleFlagOraclePort (Bits m) (smallTarget 2)

theorem base_local_safe (m : ℕ) (l : Label)
    (i : ElementaryInstruction (Bits m) (Bits m) OracleLocalWire (Bits m))
    (hi : i∈localOracleCode (labelBitsEquiv l) false) : localSafe m i := by
  have hs:=GraphEncoding.maskedOracleCircuit_safe (A := Bits m) (B := Bits m)
    2 id Function.injective_id ![(labelBitsEquiv l).1,(labelBitsEquiv l).2] false
  cases i with
  | gate g => exact hs.1 g hi
  | matrixCall p b => exact hs.2 p b hi
  | vectorCall p b =>
    simp [localOracleCode,GraphEncoding.maskedOracleCircuit,GraphEncoding.realProgramCircuit,
      elementaryMacro] at hi

theorem localCode_safe (m : ℕ) (l : Label) (second : Bool)
    (i : ElementaryInstruction (Bits m) (Bits m) OracleLocalWire (Bits m))
    (hi : i∈localCode m l second) : localSafe m i := by
  cases second with
  | false => exact base_local_safe m l i hi
  | true =>
    obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hi
    have h:=base_local_safe m l j hj
    cases j <;> exact h

def strictCircuit {m ℓ : ℕ} (c : Circuit m ℓ) : Prop :=
  safeCircuit Gate.AuxiliaryReal (singleFlagPort m ℓ) (singleFlagPort m ℓ) c

theorem queryCode_safe (m ℓ : ℕ) (l : Label) (second : Bool) :
    safeCircuit GraphEncoding.RealPhaseGate (singleFlagPort m ℓ) (singleFlagPort m ℓ)
      (queryCode m ℓ l second) := by
  intro i hi
  obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hi
  have hs:=localCode_safe m l second j hj
  cases j with
  | gate g => exact hs
  | matrixCall p b => exact congrArg (fun p=>(scratchPort (queryFrame m ℓ)).comp p) hs
  | vectorCall p b => exact congrArg (fun p=>(scratchPort (queryFrame m ℓ)).comp p) hs

theorem instruction_strict (m ℓ : ℕ) (work : WorkCircuit m) (i : SynthInstruction ℓ) :
    strictCircuit (instruction m ℓ work i) := by
  cases i with
  | query₁ =>
    exact safeCircuit_map _ _ _ _ Gate.query (fun _ h=>h) _ (queryCode_safe m ℓ .first false)
  | query₂ =>
    exact safeCircuit_map _ _ _ _ Gate.query (fun _ h=>h) _ (queryCode_safe m ℓ .second true)
  | work =>
    apply safeCircuit_map (fun _=>True) Gate.AuxiliaryReal _ _ Gate.work (fun _ h=>h)
    exact gates_only_safe _ _ _ work (fun _ _=>True.intro)
  | elementary g =>
    apply safeCircuit_map GraphEncoding.RealPhaseGate Gate.AuxiliaryReal _ _ Gate.auxiliary (fun _ h=>h)
    apply gates_only_safe
    intro k hk
    simp only [List.mem_singleton] at hk
    subst k
    exact GraphEncoding.realPhaseGate_real g
  | clock adj =>
    apply safeCircuit_map GraphEncoding.RealPhaseGate Gate.AuxiliaryReal _ _ Gate.auxiliary (fun _ h=>h)
    exact gates_only_safe _ _ _ _ (ClockGates.code_real _)

theorem compile_strict (m ℓ : ℕ) (work : WorkCircuit m) (c : SynthCircuit ℓ) :
    strictCircuit (compile m ℓ work c) := by
  intro i hi
  obtain ⟨g,hg,hi⟩:=List.mem_flatMap.mp hi
  exact instruction_strict m ℓ work g i hi

theorem compile_matrix_placement (m ℓ : ℕ) (work : WorkCircuit m) (c : SynthCircuit ℓ)
    (p : QueryPort (Bits m) (Space m ℓ)) (adj : Bool)
    (hp : NamedInstruction.matrixCall p adj∈compile m ℓ work c) :
    Nonempty (LiteralQueryPlacement (Equiv.refl (Bits m)) (coordinates m ℓ) p) := by
  have he:=compile_strict m ℓ work c (.matrixCall p adj) hp
  change p=singleFlagPort m ℓ at he
  subst p
  exact ⟨queryPlacement m ℓ⟩

theorem compile_vector_placement (m ℓ : ℕ) (work : WorkCircuit m) (c : SynthCircuit ℓ)
    (p : QueryPort (Bits m) (Space m ℓ)) (adj : Bool)
    (hp : NamedInstruction.vectorCall p adj∈compile m ℓ work c) :
    Nonempty (LiteralQueryPlacement (Equiv.refl (Bits m)) (coordinates m ℓ) p) := by
  have he:=compile_strict m ℓ work c (.vectorCall p adj) hp
  change p=singleFlagPort m ℓ at he
  subst p
  exact ⟨queryPlacement m ℓ⟩

end OptimalQLS.TransducerCompiler.Physical
