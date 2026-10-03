import OptimalQLS.Preparation.CompilerAttachment.GlobalSafety
import OptimalQLS.Preparation.CompilerAttachment.Resources
import OptimalQLS.Preparation.CompilerAttachment.Initialization

/-! # Physical elementary preparation with the exact original algorithm state -/
noncomputable section
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.Preparation.CompilerAttachment
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla

def sourcePrefix (a n ℓ : ℕ) : Circuit a n ℓ :=
  mapNamed Gate.source (sourceCall a n ℓ .pub false)

def initializationPrefix (a n ℓ : ℕ) : Circuit a n ℓ :=
  mapNamed Gate.graph (initializeGraphCircuit a n ℓ)

theorem strictCircuit_append {a n ℓ : ℕ} {c d : Circuit a n ℓ}
    (hc : strictCircuit c) (hd : strictCircuit d) : strictCircuit (c++d) := by
  intro i hi
  rcases List.mem_append.mp hi with hi|hi
  · exact hc i hi
  · exact hd i hi

theorem sourcePrefix_strict (a n ℓ : ℕ) : strictCircuit (sourcePrefix a n ℓ) := by
  apply safeCircuit_map SourceGate.Real Gate.Real _ _ Gate.source (fun _ h=>h)
  intro i hi
  cases i with
  | gate g => exact sourceCall_real a n ℓ .pub false g hi
  | matrixCall p b => exact False.elim (named_no_matrix _ _ (sourceCall_counts a n ℓ .pub false).1 p b hi)
  | vectorCall p b => exact (sourceCall_single_flag a n ℓ .pub false p b hi).1

theorem initializationPrefix_strict (a n ℓ : ℕ) : strictCircuit (initializationPrefix a n ℓ) := by
  apply safeCircuit_map GraphEncoding.RealPhaseGate Gate.Real _ _ Gate.graph (fun _ h=>h)
  intro i hi
  simp only [initializeGraphCircuit,List.mem_singleton] at hi
  subst i
  exact initializeGraphGate_real

theorem original_algorithm_lowered (a n : ℕ) {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ) :
    ∃ out : Circuit a n (preparationExponent κ), strictCircuit out ∧
      (out.toQuery (gateEval a n _ (preparationExponent_pos h))).matrixQueries=2*mainBudget κ ∧
      (out.toQuery (gateEval a n _ (preparationExponent_pos h))).vectorQueries=2*reflectionBudget κ ŝ+1 ∧
      out.workGates ≤ 436789*(a+1)*mainBudget κ+11222*(n+1)*reflectionBudget κ ŝ+2400 ∧
      ∀ UA Ub, ((out.toQuery (gateEval a n _ (preparationExponent_pos h))).eval UA Ub).val *
        basisInsertion (clean a n (preparationExponent κ))=
        basisInsertion (clean a n (preparationExponent κ))*
          ((originalPreparationAlgorithm (fun _ : Fin a=>false) (fun _ : Fin n=>false) h).eval UA Ub).val := by
  let ℓ := preparationExponent κ
  let hℓ : 0<ℓ := preparationExponent_pos h
  obtain ⟨body,hstrict,hm,hv,hg,he⟩ := compile_word_strict a n ℓ hℓ h (preparationCompiler κ ŝ)
  have hc := preparationCompiler_resources h
  rw [hc.2.1] at hm
  rw [hc.2.2.1] at hv
  have hp := sourceCall_counts a n ℓ .pub false
  let lead := sourcePrefix a n ℓ
  have hpm : (lead.toQuery (gateEval a n ℓ hℓ)).matrixQueries=0 := by
    dsimp only [lead,sourcePrefix]
    rw [mapNamed_toQuery Gate.source (sourceGateEval a n ℓ)
      (gateEval a n ℓ hℓ) (fun _=>rfl)]
    exact hp.1
  have hpv : (lead.toQuery (gateEval a n ℓ hℓ)).vectorQueries=1 := by
    dsimp only [lead,sourcePrefix]
    rw [mapNamed_toQuery Gate.source (sourceGateEval a n ℓ)
      (gateEval a n ℓ hℓ) (fun _=>rfl)]
    exact hp.2.1
  have hpg : lead.workGates≤2400 := by
    dsimp only [lead,sourcePrefix]
    rw [mapNamed_workGates]
    exact hp.2.2
  refine ⟨lead++body,strictCircuit_append (sourcePrefix_strict a n ℓ) hstrict,?_,?_,?_,?_⟩
  · change ((lead++body).toQuery (gateEval a n ℓ hℓ)).matrixQueries=_
    rw [NamedCircuit.toQuery_append,QueryCircuit.matrixQueries_append,hpm,hm,zero_add]
  · change ((lead++body).toQuery (gateEval a n ℓ hℓ)).vectorQueries=_
    rw [NamedCircuit.toQuery_append,QueryCircuit.vectorQueries_append,hpv,hv]
    omega
  · rw [NamedCircuit.workGates_append]
    rw [hc.1,hc.2.1,hc.2.2.1] at hg
    have ha := hc.2.2.2
    nlinarith [Nat.zero_le a]
  · intro UA Ub
    have hi := initialSource_intertwines a n ℓ UA Ub
    have hi' : ((lead.toQuery (gateEval a n ℓ hℓ)).eval UA Ub).val*basisInsertion (clean a n ℓ)=
        basisInsertion (clean a n ℓ)*((preparationSourcePort (Bits a) (Bits n) ℓ).apply Ub).val := by
      dsimp only [lead,sourcePrefix]
      rw [mapNamed_toQuery Gate.source (sourceGateEval a n ℓ)
        (gateEval a n ℓ hℓ) (fun _=>rfl)]
      exact hi
    have hb : ((body.toQuery (gateEval a n ℓ hℓ)).eval UA Ub).val*basisInsertion (clean a n ℓ)=
        basisInsertion (clean a n ℓ)*
          ((originalPreparationCircuit (fun _ : Fin a=>false) (fun _ : Fin n=>false) h).eval UA Ub).val := by
      rw [originalPreparationCircuit_eval]
      exact he UA Ub
    simp only [NamedCircuit.toQuery_append,QueryCircuit.eval_append,Submonoid.coe_mul]
    rw [originalPreparationAlgorithm,QueryCircuit.eval_append,Submonoid.coe_mul]
    simpa only [QueryCircuit.eval,QueryInstruction.eval,Bool.false_eq_true,ite_false,one_mul] using
      intertwines_mul _ _ _ _ _ hi' hb

/-- The actual one-gate initialized circuit starts at the all-zero physical basis,
uses the original full U_A/U_b, and produces exactly the proved preparation state
inside the clean, isometric three-scratch insertion. -/
theorem physical_prepared_state (a n : ℕ) {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ) :
    ∃ out : Circuit a n (preparationExponent κ), strictCircuit out ∧
      (out.toQuery (gateEval a n _ (preparationExponent_pos h))).matrixQueries=2*mainBudget κ ∧
      (out.toQuery (gateEval a n _ (preparationExponent_pos h))).vectorQueries=2*reflectionBudget κ ŝ+1 ∧
      out.workGates ≤ 436789*(a+1)*mainBudget κ+11222*(n+1)*reflectionBudget κ ŝ+2401 ∧
      (out.workGates : ℝ)<200000000000000*κ*(a+1)+700000000000*(κ/s)*(n+1) ∧
      ∀ UA Ub, ((out.toQuery (gateEval a n _ (preparationExponent_pos h))).eval UA Ub).val *ᵥ
        Pi.single (allZero a n (preparationExponent κ)) 1=
        basisInsertion (clean a n (preparationExponent κ))*ᵥ
          originalPreparedState (fun _ : Fin a=>false) (fun _ : Fin n=>false) h UA Ub := by
  let ℓ := preparationExponent κ
  let hℓ : 0<ℓ := preparationExponent_pos h
  obtain ⟨body,hstrict,hm,hv,hg,he⟩ := original_algorithm_lowered a n h
  let init := initializationPrefix a n ℓ
  have him : (init.toQuery (gateEval a n ℓ hℓ)).matrixQueries=0 := by
    dsimp only [init,initializationPrefix]
    rw [mapNamed_toQuery Gate.graph (graphGateEval a n ℓ)
      (gateEval a n ℓ hℓ) (fun _=>rfl)]
    exact (initializeGraphCircuit_counts a n ℓ).1
  have hiv : (init.toQuery (gateEval a n ℓ hℓ)).vectorQueries=0 := by
    dsimp only [init,initializationPrefix]
    rw [mapNamed_toQuery Gate.graph (graphGateEval a n ℓ)
      (gateEval a n ℓ hℓ) (fun _=>rfl)]
    exact (initializeGraphCircuit_counts a n ℓ).2.1
  have hig : init.workGates=1 := by
    dsimp only [init,initializationPrefix]
    rw [mapNamed_workGates]
    exact (initializeGraphCircuit_counts a n ℓ).2.2
  have hbound : (init++body).workGates ≤
      436789*(a+1)*mainBudget κ+11222*(n+1)*reflectionBudget κ ŝ+2401 := by
    rw [NamedCircuit.workGates_append,hig]
    omega
  refine ⟨init++body,strictCircuit_append (initializationPrefix_strict a n ℓ) hstrict,?_,?_,hbound,actual_gate_bound a n _ h hbound,?_⟩
  · change ((init++body).toQuery (gateEval a n ℓ hℓ)).matrixQueries=_
    rw [NamedCircuit.toQuery_append,QueryCircuit.matrixQueries_append,him,zero_add]
    exact hm
  · change ((init++body).toQuery (gateEval a n ℓ hℓ)).vectorQueries=_
    rw [NamedCircuit.toQuery_append,QueryCircuit.vectorQueries_append,hiv,zero_add]
    exact hv
  · intro UA Ub
    have hi : ((init.toQuery (gateEval a n ℓ hℓ)).eval UA Ub).val*ᵥ
        Pi.single (allZero a n ℓ) 1=basisInsertion (clean a n ℓ)*ᵥ
          preparationBasisInput (fun _ : Fin a=>false) (fun _ : Fin n=>false) h := by
      dsimp only [init,initializationPrefix]
      rw [mapNamed_toQuery Gate.graph (graphGateEval a n ℓ)
        (gateEval a n ℓ hℓ) (fun _=>rfl)]
      exact initializeGraphCircuit_state a n h UA Ub
    rw [NamedCircuit.toQuery_append,QueryCircuit.eval_append,Submonoid.coe_mul,
      ← Matrix.mulVec_mulVec,hi,Matrix.mulVec_mulVec,he UA Ub,← Matrix.mulVec_mulVec]
    rfl

end OptimalQLS.Preparation.CompilerAttachment
