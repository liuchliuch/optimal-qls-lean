import OptimalQLS.Preparation.CompilerAttachment.FullCompiler
import OptimalQLS.Preparation.CompilerAttachment.SourceSafety

/-! # Real elementary leaves and strict single-bit oracle ports of the full compiler -/
noncomputable section
namespace OptimalQLS.Preparation.CompilerAttachment
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
open scoped Classical

def Gate.Real {a n ℓ : ℕ} : Gate a n ℓ → Prop
  | .auxiliary g => GraphEncoding.RealPhaseGate g
  | .graph g => GraphEncoding.RealPhaseGate g
  | .source g => g.Real
  | .work g => WorkGates.RealGate g

theorem gate_real {a n ℓ : ℕ} (hℓ : 0<ℓ) (g : Gate a n ℓ) (hg : g.Real) :
    ∀ i j, ((gateEval a n ℓ hℓ g).val i j).im=0 := by
  cases g with
  | auxiliary g => exact GateSynthesis.placeHom_real _ _ hg
  | graph g => exact GateSynthesis.placeHom_real _ _ (GateSynthesis.placeHom_real _ _ hg)
  | source g => exact sourceGate_real a n ℓ g hg
  | work g =>
    cases ℓ with
    | zero => omega
    | succ ℓ => exact GateSynthesis.placeHom_real _ _ (GateSynthesis.placeHom_real _ _ hg)

variable {G H A B P : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype P] [DecidableEq P]

def safeInstruction (R : G → Prop) (ma : QueryPort A P) (vb : QueryPort B P) :
    NamedInstruction G A B P → Prop
  | .gate g => R g
  | .matrixCall p _ => p=ma
  | .vectorCall p _ => p=vb

def safeCircuit (R : G → Prop) (ma : QueryPort A P) (vb : QueryPort B P)
    (c : NamedCircuit G A B P) : Prop := ∀ i∈c, safeInstruction R ma vb i

theorem safeCircuit_map (R : G → Prop) (T : H → Prop) (ma : QueryPort A P) (vb : QueryPort B P)
    (f : G → H) (hf : ∀ g,R g→T (f g)) (c : NamedCircuit G A B P)
    (hc : safeCircuit R ma vb c) : safeCircuit T ma vb (mapNamed f c) := by
  intro i hi
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  have hs := hc j hj
  cases j with
  | gate g => exact hf g hs
  | matrixCall p b => exact hs
  | vectorCall p b => exact hs

theorem named_no_matrix (e : G → Matrix.unitaryGroup P ℂ) (c : NamedCircuit G A B P)
    (h : (c.toQuery e).matrixQueries=0) (p : QueryPort A P) (b : Bool) :
    NamedInstruction.matrixCall p b ∉ c := by
  induction c with
  | nil => simp
  | cons g c ih =>
    cases g <;> simp only [NamedCircuit.toQuery,NamedInstruction.toQuery,List.map_cons,
      QueryCircuit.matrixQueries] at h <;> simp_all <;> exact ih h

theorem named_no_vector (e : G → Matrix.unitaryGroup P ℂ) (c : NamedCircuit G A B P)
    (h : (c.toQuery e).vectorQueries=0) (p : QueryPort B P) (b : Bool) :
    NamedInstruction.vectorCall p b ∉ c := by
  induction c with
  | nil => simp
  | cons g c ih =>
    cases g <;> simp only [NamedCircuit.toQuery,NamedInstruction.toQuery,List.map_cons,
      QueryCircuit.vectorQueries] at h <;> simp_all <;> exact ih h

def strictCircuit {a n ℓ : ℕ} (c : Circuit a n ℓ) : Prop :=
  safeCircuit Gate.Real (graphSingleFlagPort a n ℓ) (sourceSingleFlagPort a n ℓ) c

theorem gates_only_safe (R : G → Prop) (ma : QueryPort A P) (vb : QueryPort B P)
    (code : List G) (h : ∀ g∈code,R g) :
    safeCircuit R ma vb (code.map NamedInstruction.gate) := by
  intro i hi
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hi
  exact h g hg

theorem instruction_strict (a n ℓ : ℕ) {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ)
    (graph : GraphCircuit a n ℓ)
    (hr : ∀ g,NamedInstruction.gate g∈graph→GraphEncoding.RealPhaseGate g)
    (hm : ∀ p b,NamedInstruction.matrixCall p b∈graph→p=graphSingleFlagPort a n ℓ)
    (hv : (graph.toQuery (graphGateEval a n ℓ)).vectorQueries=0)
    (i : SynthInstruction ℓ) : strictCircuit (instruction a n ℓ h graph i) := by
  cases i with
  | query₁ =>
    apply safeCircuit_map GraphEncoding.RealPhaseGate Gate.Real _ _ Gate.graph (fun _ h=>h)
    intro i hi
    cases i with
    | gate g => exact hr g hi
    | matrixCall p b => exact hm p b hi
    | vectorCall p b => exact False.elim (named_no_vector _ _ hv p b hi)
  | query₂ =>
    apply safeCircuit_map SourceGate.Real Gate.Real _ _ Gate.source (fun _ h=>h)
    intro i hi
    cases i with
    | gate g => exact compilerReflectionCall_real a n ℓ g hi
    | matrixCall p b =>
      exact False.elim (named_no_matrix _ _ (compilerReflectionCall_counts a n ℓ).1 p b hi)
    | vectorCall p b => exact compilerReflectionCall_single_flag a n ℓ p b hi
  | work =>
    apply safeCircuit_map WorkGates.RealGate Gate.Real _ _ Gate.work (fun _ h=>h)
    exact gates_only_safe _ _ _ _ (compiledWorkProgram_real (a+4) _ _ true)
  | elementary g =>
    apply safeCircuit_map GraphEncoding.RealPhaseGate Gate.Real _ _ Gate.auxiliary (fun _ h=>h)
    apply gates_only_safe
    intro k hk
    simp only [List.mem_singleton] at hk
    subst k
    exact GraphEncoding.realPhaseGate_real g
  | clock b =>
    apply safeCircuit_map GraphEncoding.RealPhaseGate Gate.Real _ _ Gate.auxiliary (fun _ h=>h)
    exact gates_only_safe _ _ _ _ (ClockGates.code_real _)

theorem macroCompile_strict (a n ℓ : ℕ) {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ)
    (graph : GraphCircuit a n ℓ)
    (hr : ∀ g,NamedInstruction.gate g∈graph→GraphEncoding.RealPhaseGate g)
    (hm : ∀ p b,NamedInstruction.matrixCall p b∈graph→p=graphSingleFlagPort a n ℓ)
    (hv : (graph.toQuery (graphGateEval a n ℓ)).vectorQueries=0)
    (c : SynthCircuit ℓ) : strictCircuit (macroCompile (instruction a n ℓ h graph) c) := by
  intro i hi
  obtain ⟨g,hg,hi⟩ := List.mem_flatMap.mp hi
  exact instruction_strict a n ℓ h graph hr hm hv g i hi

/-- All emitted original-oracle controls read exactly one fixed named flag. -/
theorem strictCircuit_ports {a n ℓ : ℕ} (c : Circuit a n ℓ) (hc : strictCircuit c) :
    (∀ p b,NamedInstruction.matrixCall p b∈c→p=graphSingleFlagPort a n ℓ) ∧
    (∀ p b,NamedInstruction.vectorCall p b∈c→p=sourceSingleFlagPort a n ℓ) ∧
    (∀ g,NamedInstruction.gate g∈c→g.arity≤2 ∧ g.Real) := by
  refine ⟨fun p b hp=>hc _ hp,fun p b hp=>hc _ hp,?_⟩
  intro g hg
  exact ⟨Gate.arity_le_two g,hc _ hg⟩

theorem compile_word_strict (a n ℓ : ℕ) (hℓ : 0<ℓ) {κ s ŝ : ℝ}
    (h : BudgetParameters κ s ŝ) (c : SynthCircuit ℓ) :
    ∃ out : Circuit a n ℓ, strictCircuit out ∧
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
  obtain ⟨graph,hm,hv,hg,hr,hports,he⟩ := graphCompilerCall a n ℓ κ h.kappa_pos
  let p := instruction a n ℓ h graph
  have hc := macroCompile_counts (gateEval a n ℓ hℓ) p (183375*(a+1)) 252304 (11222*(n+1))
    (instruction_counts a n ℓ hℓ h graph ⟨hm,hv,hg⟩) c
  refine ⟨macroCompile p c,macroCompile_strict a n ℓ h graph hr hports hv c,
    hc.1,hc.2.1,hc.2.2,?_⟩
  intro UA Ub
  exact macroCompile_intertwines (gateEval a n ℓ hℓ) p _ _ _ (basisInsertion (clean a n ℓ))
    (instruction_intertwines a n ℓ hℓ h graph he) c UA Ub

end OptimalQLS.Preparation.CompilerAttachment
