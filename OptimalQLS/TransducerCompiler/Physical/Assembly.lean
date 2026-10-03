import OptimalQLS.TransducerCompiler.Physical.Queries
import OptimalQLS.TransducerCompiler.Physical.Auxiliary
import OptimalQLS.Preparation.CompilerAttachment.ListAssembly

/-! Literal complete macro expansion, preserving both original oracle counts. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.TransducerCompiler.Physical
open Matrix BinaryClock PolynomialTransform DirtyAncilla
open Preparation.CompilerAttachment

section Bookkeeping
variable {G A B P : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype P] [DecidableEq P]

theorem macroCompile_single_counts {ℓ : ℕ} (gate : G → Matrix.unitaryGroup P ℂ)
    (p : SynthInstruction ℓ → NamedCircuit G A B P) (W F R : ℕ)
    (hp : ∀ g, (p g |>.toQuery gate).matrixQueries=g.firstCost ∧
      (p g |>.toQuery gate).vectorQueries=g.secondCost ∧
      (p g).workGates ≤ instructionGateBudget W F R g)
    (c : SynthCircuit ℓ) :
    ((macroCompile p c).toQuery gate).matrixQueries=c.firstCalls ∧
      ((macroCompile p c).toQuery gate).vectorQueries=c.secondCalls ∧
      (macroCompile p c).workGates≤c.auxGates+W*c.workCalls+F*c.firstCalls+R*c.secondCalls := by
  have aux (c : SynthCircuit ℓ) :
      ((macroCompile p c).toQuery gate).matrixQueries=c.firstCalls ∧
      ((macroCompile p c).toQuery gate).vectorQueries=c.secondCalls ∧
      (macroCompile p c).workGates≤listGateBudget W F R c := by
    induction c with
    | nil => simp [macroCompile,NamedCircuit.toQuery,QueryCircuit.matrixQueries,
        QueryCircuit.vectorQueries,SynthCircuit.firstCalls,SynthCircuit.secondCalls,
        NamedCircuit.workGates,listGateBudget]
    | cons g c ih =>
      have hg := hp g
      simp only [macroCompile,List.flatMap_cons,NamedCircuit.toQuery_append,
        QueryCircuit.matrixQueries_append,QueryCircuit.vectorQueries_append,
        NamedCircuit.workGates_append]
      change (p g |>.toQuery gate).matrixQueries+((macroCompile p c).toQuery gate).matrixQueries=_ ∧
        (p g |>.toQuery gate).vectorQueries+((macroCompile p c).toQuery gate).vectorQueries=_ ∧
        (p g).workGates+(macroCompile p c).workGates≤_
      rw [hg.1,ih.1,hg.2.1,ih.2.1]
      simp only [SynthCircuit.firstCalls,SynthCircuit.secondCalls,List.map_cons,List.sum_cons,
        listGateBudget,Nat.mul_add]
      exact ⟨trivial,trivial,Nat.add_le_add hg.2.2 ih.2.2⟩
  simpa only [listGateBudget_eq] using aux c

end Bookkeeping

inductive Gate (m ℓ : ℕ) where
  | work (g : LocalGate (workCoordinates m))
  | auxiliary (g : PhaseGate (LabelWire ℓ))
  | query (g : PhaseGate OracleLocalWire)

def gateEval (m ℓ : ℕ) (hℓ : 0<ℓ) : Gate m ℓ → Matrix.unitaryGroup (Space m ℓ) ℂ
  | .work g => workGateEval m ℓ hℓ g
  | .auxiliary g => auxGateEval m ℓ g
  | .query g => queryGateEval m ℓ g

abbrev Circuit (m ℓ : ℕ) := NamedCircuit (Gate m ℓ) (Bits m) (Bits m) (Space m ℓ)

def instruction (m ℓ : ℕ) (work : WorkCircuit m) : SynthInstruction ℓ → Circuit m ℓ
  | .query₁ => mapNamed Gate.query (queryCode m ℓ .first false)
  | .query₂ => mapNamed Gate.query (queryCode m ℓ .second true)
  | .work => mapNamed Gate.work (workCode m ℓ work)
  | .elementary g => mapNamed Gate.auxiliary (auxCode m ℓ [.real g])
  | .clock _ => mapNamed Gate.auxiliary (auxCode m ℓ (ClockGates.labelCode ℓ))

theorem instruction_counts (m ℓ : ℕ) (hℓ : 0<ℓ) (work : WorkCircuit m)
    (g : SynthInstruction ℓ) :
    ((instruction m ℓ work g).toQuery (gateEval m ℓ hℓ)).matrixQueries=g.firstCost ∧
    ((instruction m ℓ work g).toQuery (gateEval m ℓ hℓ)).vectorQueries=g.secondCost ∧
    (instruction m ℓ work g).workGates≤ instructionGateBudget work.length 2400 2400 g := by
  cases g with
  | query₁ =>
    rw [instruction,mapNamed_toQuery Gate.query (queryGateEval m ℓ) (gateEval m ℓ hℓ) (fun _=>rfl),
      mapNamed_workGates]
    exact queryCode_counts m ℓ .first false
  | query₂ =>
    rw [instruction,mapNamed_toQuery Gate.query (queryGateEval m ℓ) (gateEval m ℓ hℓ) (fun _=>rfl),
      mapNamed_workGates]
    exact queryCode_counts m ℓ .second true
  | work =>
    rw [instruction,mapNamed_toQuery Gate.work (workGateEval m ℓ hℓ) (gateEval m ℓ hℓ) (fun _=>rfl),
      mapNamed_workGates]
    have h:=workCode_counts m ℓ hℓ work
    exact ⟨h.1,h.2.1,h.2.2.le⟩
  | elementary g =>
    rw [instruction,mapNamed_toQuery Gate.auxiliary (auxGateEval m ℓ) (gateEval m ℓ hℓ) (fun _=>rfl),
      mapNamed_workGates]
    have h:=auxCode_counts m ℓ [.real g]
    exact ⟨h.1,h.2.1,h.2.2.le⟩
  | clock adj =>
    rw [instruction,mapNamed_toQuery Gate.auxiliary (auxGateEval m ℓ) (gateEval m ℓ hℓ) (fun _=>rfl),
      mapNamed_workGates]
    have h:=auxCode_counts m ℓ (ClockGates.labelCode ℓ)
    exact ⟨h.1,h.2.1,by simpa only [ClockGates.labelCode,ClockGates.code_length,instructionGateBudget] using h.2.2.le⟩

theorem instruction_intertwines (m ℓ : ℕ) (hℓ : 0<ℓ)
    (S : Matrix.unitaryGroup (Base (Bits m)) ℂ) (work : WorkCircuit m)
    (hw : ControlledWork S work) (g : SynthInstruction ℓ)
    (U₁ U₂ : Matrix.unitaryGroup (Bits m) ℂ) :
    (((instruction m ℓ work g).toQuery (gateEval m ℓ hℓ)).eval U₁ U₂).val*
      basisInsertion (clean m ℓ)=basisInsertion (clean m ℓ)*(g.eval S U₁ U₂).val := by
  cases g with
  | query₁ =>
    rw [instruction,mapNamed_toQuery Gate.query (queryGateEval m ℓ) (gateEval m ℓ hℓ) (fun _=>rfl)]
    exact queryCode_intertwines m ℓ .first false U₁ U₂
  | query₂ =>
    rw [instruction,mapNamed_toQuery Gate.query (queryGateEval m ℓ) (gateEval m ℓ hℓ) (fun _=>rfl)]
    exact queryCode_intertwines m ℓ .second true U₁ U₂
  | work =>
    rw [instruction,mapNamed_toQuery Gate.work (workGateEval m ℓ hℓ) (gateEval m ℓ hℓ) (fun _=>rfl)]
    exact workCode_intertwines m ℓ hℓ S work hw U₁ U₂
  | elementary g =>
    rw [instruction,mapNamed_toQuery Gate.auxiliary (auxGateEval m ℓ) (gateEval m ℓ hℓ) (fun _=>rfl)]
    simpa only [phaseEval,one_mul,PhaseGate.eval] using auxCode_intertwines m ℓ [.real g] U₁ U₂
  | clock adj =>
    rw [instruction,mapNamed_toQuery Gate.auxiliary (auxGateEval m ℓ) (gateEval m ℓ hℓ) (fun _=>rfl)]
    exact clock_intertwines m ℓ adj S U₁ U₂

def compile (m ℓ : ℕ) (work : WorkCircuit m) (c : SynthCircuit ℓ) : Circuit m ℓ :=
  macroCompile (instruction m ℓ work) c

theorem compile_counts (m ℓ : ℕ) (hℓ : 0<ℓ) (work : WorkCircuit m) (c : SynthCircuit ℓ) :
    ((compile m ℓ work c).toQuery (gateEval m ℓ hℓ)).matrixQueries=c.firstCalls ∧
    ((compile m ℓ work c).toQuery (gateEval m ℓ hℓ)).vectorQueries=c.secondCalls ∧
    (compile m ℓ work c).workGates≤c.auxGates+work.length*c.workCalls+
      2400*c.firstCalls+2400*c.secondCalls :=
  macroCompile_single_counts (gateEval m ℓ hℓ) (instruction m ℓ work) work.length 2400 2400
    (instruction_counts m ℓ hℓ work) c

theorem compile_intertwines (m ℓ : ℕ) (hℓ : 0<ℓ)
    (S : Matrix.unitaryGroup (Base (Bits m)) ℂ) (work : WorkCircuit m)
    (hw : ControlledWork S work) (c : SynthCircuit ℓ) (U₁ U₂ : Matrix.unitaryGroup (Bits m) ℂ) :
    (((compile m ℓ work c).toQuery (gateEval m ℓ hℓ)).eval U₁ U₂).val*
      basisInsertion (clean m ℓ)=basisInsertion (clean m ℓ)*(c.eval S U₁ U₂).val :=
  macroCompile_intertwines (gateEval m ℓ hℓ) (instruction m ℓ work) S id id
    (basisInsertion (clean m ℓ)) (instruction_intertwines m ℓ hℓ S work hw) c U₁ U₂

end OptimalQLS.TransducerCompiler.Physical
