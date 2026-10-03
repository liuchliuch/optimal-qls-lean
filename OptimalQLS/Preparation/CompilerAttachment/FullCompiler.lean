import OptimalQLS.Preparation.CompilerAttachment.WorkGates
import OptimalQLS.Preparation.CompilerAttachment.SourceSemantics
import OptimalQLS.Preparation.CompilerAttachment.AuxiliaryGates

/-! # Literal elementary lowering of every actual preparationCompiler instruction -/
noncomputable section
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.Preparation.CompilerAttachment
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla

/-- Each constructor carries only already physically placed one/two-qubit leaves. -/
inductive Gate (a n ℓ : ℕ) where
  | auxiliary (g : PhaseGate (LabelWire ℓ))
  | graph (g : PhaseGate GraphLocalWire)
  | source (g : SourceGate n)
  | work (g : WorkGate a)

def gateEval (a n ℓ : ℕ) (hℓ : 0<ℓ) : Gate a n ℓ → Matrix.unitaryGroup (Physical a n ℓ) ℂ
  | .auxiliary g => auxiliaryGateEval a n ℓ g
  | .graph g => graphGateEval a n ℓ g
  | .source g => sourceGateEval a n ℓ g
  | .work g => positiveWorkGateEval a n ℓ hℓ g

def Gate.arity {a n ℓ : ℕ} : Gate a n ℓ → ℕ
  | .auxiliary g => g.arity
  | .graph g => g.arity
  | .source g => g.arity
  | .work g => g.arity

theorem Gate.arity_le_two {a n ℓ : ℕ} (g : Gate a n ℓ) : g.arity≤2 := by
  cases g with
  | auxiliary g => exact PhaseGate.arity_le_two _
  | graph g => exact PhaseGate.arity_le_two _
  | source g => exact SourceGate.arity_le_two _
  | work g => exact PhaseGate.arity_le_two _

abbrev Circuit (a n ℓ : ℕ) := NamedCircuit (Gate a n ℓ) (Bits a × Bits n) (Bits n) (Physical a n ℓ)
abbrev GraphCircuit (a n ℓ : ℕ) :=
  NamedCircuit (PhaseGate GraphLocalWire) (Bits a × Bits n) (Bits n) (Physical a n ℓ)

def instruction (a n ℓ : ℕ) {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ)
    (graph : GraphCircuit a n ℓ) : SynthInstruction ℓ → Circuit a n ℓ
  | .query₁ => mapNamed Gate.graph graph
  | .query₂ => mapNamed Gate.source (compilerReflectionCall a n ℓ)
  | .work => mapNamed Gate.work (positiveWorkMacro a n ℓ (preparationWorkCode a h))
  | .elementary g => mapNamed Gate.auxiliary (auxiliaryMacro a n ℓ [.real g])
  | .clock _ => mapNamed Gate.auxiliary (auxiliaryMacro a n ℓ (ClockGates.labelCode ℓ))

theorem instruction_first_counts (a n ℓ : ℕ) (hℓ : 0<ℓ) {κ s ŝ : ℝ}
    (h : BudgetParameters κ s ŝ) (graph : GraphCircuit a n ℓ)
    (hgraph : (graph.toQuery (graphGateEval a n ℓ)).matrixQueries=2 ∧
      (graph.toQuery (graphGateEval a n ℓ)).vectorQueries=0 ∧ graph.workGates≤252304)
 :
    ((instruction a n ℓ h graph (.query₁ : SynthInstruction ℓ)).toQuery (gateEval a n ℓ hℓ)).matrixQueries=2*(.query₁ : SynthInstruction ℓ).firstCost ∧
      ((instruction a n ℓ h graph (.query₁ : SynthInstruction ℓ)).toQuery (gateEval a n ℓ hℓ)).vectorQueries=2*(.query₁ : SynthInstruction ℓ).secondCost ∧
      (instruction a n ℓ h graph (.query₁ : SynthInstruction ℓ)).workGates ≤
        instructionGateBudget (183375*(a+1)) 252304 (11222*(n+1)) (.query₁ : SynthInstruction ℓ) := by
  rw [instruction,mapNamed_toQuery Gate.graph (graphGateEval a n ℓ) (gateEval a n ℓ hℓ) (fun _=>rfl),
    mapNamed_workGates]
  norm_num only [instructionGateBudget,SynthInstruction.firstCost,SynthInstruction.secondCost,
    SynthInstruction.workCost,SynthInstruction.auxCost,Nat.mul_one,Nat.mul_zero,Nat.zero_add,Nat.add_zero]
  exact hgraph


theorem instruction_second_counts (a n ℓ : ℕ) (hℓ : 0<ℓ) {κ s ŝ : ℝ}
    (h : BudgetParameters κ s ŝ) (graph : GraphCircuit a n ℓ)
    (hgraph : (graph.toQuery (graphGateEval a n ℓ)).matrixQueries=2 ∧
      (graph.toQuery (graphGateEval a n ℓ)).vectorQueries=0 ∧ graph.workGates≤252304)
 :
    ((instruction a n ℓ h graph (.query₂ : SynthInstruction ℓ)).toQuery (gateEval a n ℓ hℓ)).matrixQueries=2*(.query₂ : SynthInstruction ℓ).firstCost ∧
      ((instruction a n ℓ h graph (.query₂ : SynthInstruction ℓ)).toQuery (gateEval a n ℓ hℓ)).vectorQueries=2*(.query₂ : SynthInstruction ℓ).secondCost ∧
      (instruction a n ℓ h graph (.query₂ : SynthInstruction ℓ)).workGates ≤
        instructionGateBudget (183375*(a+1)) 252304 (11222*(n+1)) (.query₂ : SynthInstruction ℓ) := by
  rw [instruction,mapNamed_toQuery Gate.source (sourceGateEval a n ℓ) (gateEval a n ℓ hℓ) (fun _=>rfl),
    mapNamed_workGates]
  norm_num only [instructionGateBudget,SynthInstruction.firstCost,SynthInstruction.secondCost,
    SynthInstruction.workCost,SynthInstruction.auxCost,Nat.mul_one,Nat.mul_zero,Nat.zero_add,Nat.add_zero]
  exact compilerReflectionCall_counts a n ℓ


theorem instruction_work_counts (a n ℓ : ℕ) (hℓ : 0<ℓ) {κ s ŝ : ℝ}
    (h : BudgetParameters κ s ŝ) (graph : GraphCircuit a n ℓ)
    (hgraph : (graph.toQuery (graphGateEval a n ℓ)).matrixQueries=2 ∧
      (graph.toQuery (graphGateEval a n ℓ)).vectorQueries=0 ∧ graph.workGates≤252304)
 :
    ((instruction a n ℓ h graph (.work : SynthInstruction ℓ)).toQuery (gateEval a n ℓ hℓ)).matrixQueries=2*(.work : SynthInstruction ℓ).firstCost ∧
      ((instruction a n ℓ h graph (.work : SynthInstruction ℓ)).toQuery (gateEval a n ℓ hℓ)).vectorQueries=2*(.work : SynthInstruction ℓ).secondCost ∧
      (instruction a n ℓ h graph (.work : SynthInstruction ℓ)).workGates ≤
        instructionGateBudget (183375*(a+1)) 252304 (11222*(n+1)) (.work : SynthInstruction ℓ) := by
  have hc := positiveWorkMacro_counts a n ℓ hℓ (preparationWorkCode a h)
  have hb := preparationWorkCode_length a h
  simpa only [instruction,mapNamed_toQuery Gate.work (positiveWorkGateEval a n ℓ hℓ) (gateEval a n ℓ hℓ)
    (fun _=>rfl),mapNamed_workGates,instructionGateBudget,SynthInstruction.firstCost,
    SynthInstruction.secondCost,SynthInstruction.workCost,SynthInstruction.auxCost,
    Nat.mul_one,Nat.mul_zero,Nat.zero_add,Nat.add_zero] using
    And.intro hc.1 (And.intro hc.2.1 (hc.2.2.le.trans hb))

theorem instruction_elementary_counts (a n ℓ : ℕ) (hℓ : 0<ℓ) {κ s ŝ : ℝ}
    (h : BudgetParameters κ s ŝ) (graph : GraphCircuit a n ℓ)
    (hgraph : (graph.toQuery (graphGateEval a n ℓ)).matrixQueries=2 ∧
      (graph.toQuery (graphGateEval a n ℓ)).vectorQueries=0 ∧ graph.workGates≤252304)
    (g : GateSynthesis.LowerGate (LabelWire ℓ)) :
    ((instruction a n ℓ h graph (.elementary g : SynthInstruction ℓ)).toQuery (gateEval a n ℓ hℓ)).matrixQueries=2*(.elementary g : SynthInstruction ℓ).firstCost ∧
      ((instruction a n ℓ h graph (.elementary g : SynthInstruction ℓ)).toQuery (gateEval a n ℓ hℓ)).vectorQueries=2*(.elementary g : SynthInstruction ℓ).secondCost ∧
      (instruction a n ℓ h graph (.elementary g : SynthInstruction ℓ)).workGates ≤
        instructionGateBudget (183375*(a+1)) 252304 (11222*(n+1)) (.elementary g : SynthInstruction ℓ) := by
  have hc := auxiliaryMacro_queries (A := Bits a × Bits n) (B := Bits n) a n ℓ [.real g]
  simpa [instruction,mapNamed_toQuery Gate.auxiliary (auxiliaryGateEval a n ℓ) (gateEval a n ℓ hℓ)
    (fun _=>rfl),mapNamed_workGates,auxiliaryMacro_workGates,instructionGateBudget,
    SynthInstruction.firstCost,SynthInstruction.secondCost,SynthInstruction.workCost,
    SynthInstruction.auxCost] using And.intro hc.1 hc.2

theorem instruction_clock_counts (a n ℓ : ℕ) (hℓ : 0<ℓ) {κ s ŝ : ℝ}
    (h : BudgetParameters κ s ŝ) (graph : GraphCircuit a n ℓ)
    (hgraph : (graph.toQuery (graphGateEval a n ℓ)).matrixQueries=2 ∧
      (graph.toQuery (graphGateEval a n ℓ)).vectorQueries=0 ∧ graph.workGates≤252304)
    (adj : Bool) :
    ((instruction a n ℓ h graph (.clock adj : SynthInstruction ℓ)).toQuery (gateEval a n ℓ hℓ)).matrixQueries=2*(.clock adj : SynthInstruction ℓ).firstCost ∧
      ((instruction a n ℓ h graph (.clock adj : SynthInstruction ℓ)).toQuery (gateEval a n ℓ hℓ)).vectorQueries=2*(.clock adj : SynthInstruction ℓ).secondCost ∧
      (instruction a n ℓ h graph (.clock adj : SynthInstruction ℓ)).workGates ≤
        instructionGateBudget (183375*(a+1)) 252304 (11222*(n+1)) (.clock adj : SynthInstruction ℓ) := by
  have hc := auxiliaryMacro_queries (A := Bits a × Bits n) (B := Bits n) a n ℓ (ClockGates.labelCode ℓ)
  simpa [instruction,mapNamed_toQuery Gate.auxiliary (auxiliaryGateEval a n ℓ) (gateEval a n ℓ hℓ)
    (fun _=>rfl),mapNamed_workGates,auxiliaryMacro_workGates,instructionGateBudget,
    SynthInstruction.firstCost,SynthInstruction.secondCost,SynthInstruction.workCost,
    SynthInstruction.auxCost] using And.intro hc.1 hc.2

theorem instruction_counts (a n ℓ : ℕ) (hℓ : 0<ℓ) {κ s ŝ : ℝ}
    (h : BudgetParameters κ s ŝ) (graph : GraphCircuit a n ℓ)
    (hgraph : (graph.toQuery (graphGateEval a n ℓ)).matrixQueries=2 ∧
      (graph.toQuery (graphGateEval a n ℓ)).vectorQueries=0 ∧ graph.workGates≤252304)
    (g : SynthInstruction ℓ) :
    ((instruction a n ℓ h graph g).toQuery (gateEval a n ℓ hℓ)).matrixQueries=2*g.firstCost ∧
      ((instruction a n ℓ h graph g).toQuery (gateEval a n ℓ hℓ)).vectorQueries=2*g.secondCost ∧
      (instruction a n ℓ h graph g).workGates ≤
        instructionGateBudget (183375*(a+1)) 252304 (11222*(n+1)) g := by
  cases g with
  | query₁ => exact instruction_first_counts a n ℓ hℓ h graph hgraph
  | query₂ => exact instruction_second_counts a n ℓ hℓ h graph hgraph
  | work => exact instruction_work_counts a n ℓ hℓ h graph hgraph
  | elementary g => exact instruction_elementary_counts a n ℓ hℓ h graph hgraph g
  | clock adj => exact instruction_clock_counts a n ℓ hℓ h graph hgraph adj

theorem instruction_intertwines (a n ℓ : ℕ) (hℓ : 0<ℓ) {κ s ŝ : ℝ}
    (h : BudgetParameters κ s ŝ) (graph : GraphCircuit a n ℓ)
    (hgraph : ∀ UA Ub, ((graph.toQuery (graphGateEval a n ℓ)).eval UA Ub).val*basisInsertion (clean a n ℓ)=
      basisInsertion (clean a n ℓ)*
        ((compilerDataPort (PreparationData (Bits a) (Bits n)) ℓ .first).apply
          (doubleOracle (GraphEncoding.physicalEncoding κ h.kappa_pos UA))).val)
    (g : SynthInstruction ℓ) (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    (((instruction a n ℓ h graph g).toQuery (gateEval a n ℓ hℓ)).eval UA Ub).val*
      basisInsertion (clean a n ℓ)=
    basisInsertion (clean a n ℓ)*
      (g.eval (finitePreparationWork (D := Fin 4 × Bits n)
          (GraphEncoding.physicalSignalZero (fun _ : Fin a=>false)) h
          (by have := h.kappa_pos; positivity : 0<1+κ⁻¹))
        (doubleOracle (GraphEncoding.physicalEncoding κ h.kappa_pos UA))
        (doubleOracle (signalLift (S := GraphEncoding.PhysicalSignal (Bits a))
          (preparedReflection (signalLift (S := Fin 4) Ub) (1,fun _=>false))))).val := by
  cases g with
  | query₁ =>
    rw [instruction,mapNamed_toQuery Gate.graph (graphGateEval a n ℓ) (gateEval a n ℓ hℓ) (fun _=>rfl)]
    simpa only [compilerDataPort_eval] using hgraph UA Ub
  | query₂ =>
    rw [instruction,mapNamed_toQuery Gate.source (sourceGateEval a n ℓ) (gateEval a n ℓ hℓ) (fun _=>rfl)]
    simpa only [compilerDataPort_eval] using compilerReflectionCall_intertwines a n ℓ UA Ub
  | work =>
    rw [instruction,mapNamed_toQuery Gate.work (positiveWorkGateEval a n ℓ hℓ) (gateEval a n ℓ hℓ) (fun _=>rfl)]
    exact positiveWorkMacro_intertwines a n ℓ hℓ h UA Ub
  | elementary g =>
    rw [instruction,mapNamed_toQuery Gate.auxiliary (auxiliaryGateEval a n ℓ) (gateEval a n ℓ hℓ) (fun _=>rfl),
      auxiliaryMacro_eval]
    simpa only [phaseEval,one_mul,PhaseGate.eval] using auxiliaryPlacement_clean a n ℓ g.eval
  | clock adj =>
    rw [instruction,mapNamed_toQuery Gate.auxiliary (auxiliaryGateEval a n ℓ) (gateEval a n ℓ hℓ) (fun _=>rfl),
      auxiliaryMacro_eval]
    exact auxiliaryClock_intertwines a n ℓ adj _ _ _

/-- A literal circuit for any actual compiler word, with actual emitted gate counts. -/
theorem compile_word (a n ℓ : ℕ) (hℓ : 0<ℓ) {κ s ŝ : ℝ}
    (h : BudgetParameters κ s ŝ) (c : SynthCircuit ℓ) :
    ∃ out : Circuit a n ℓ,
      (out.toQuery (gateEval a n ℓ hℓ)).matrixQueries=2*c.firstCalls ∧
      (out.toQuery (gateEval a n ℓ hℓ)).vectorQueries=2*c.secondCalls ∧
      out.workGates ≤ c.auxGates+183375*(a+1)*c.workCalls+252304*c.firstCalls+
        11222*(n+1)*c.secondCalls ∧
      ∀ UA Ub, ((out.toQuery (gateEval a n ℓ hℓ)).eval UA Ub).val*basisInsertion (clean a n ℓ)=
        basisInsertion (clean a n ℓ)*
          (c.eval (finitePreparationWork (D := Fin 4 × Bits n)
              (GraphEncoding.physicalSignalZero (fun _ : Fin a=>false)) h
              (by have := h.kappa_pos; positivity : 0<1+κ⁻¹))
            (doubleOracle (GraphEncoding.physicalEncoding κ h.kappa_pos UA))
            (doubleOracle (signalLift (S := GraphEncoding.PhysicalSignal (Bits a))
              (preparedReflection (signalLift (S := Fin 4) Ub) (1,fun _=>false))))).val := by
  obtain ⟨graph,hm,hv,hg,_,_,he⟩ := graphCompilerCall a n ℓ κ h.kappa_pos
  let p := instruction a n ℓ h graph
  have hc := macroCompile_counts (gateEval a n ℓ hℓ) p (183375*(a+1)) 252304 (11222*(n+1))
    (instruction_counts a n ℓ hℓ h graph ⟨hm,hv,hg⟩) c
  refine ⟨macroCompile p c,hc.1,hc.2.1,hc.2.2,?_⟩
  intro UA Ub
  exact macroCompile_intertwines (gateEval a n ℓ hℓ) p _ _ _ (basisInsertion (clean a n ℓ))
    (instruction_intertwines a n ℓ hℓ h graph he) c UA Ub

end OptimalQLS.Preparation.CompilerAttachment
