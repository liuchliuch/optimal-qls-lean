import OptimalQLS.Preparation.CompilerAttachment.FlagReadout
import OptimalQLS.Preparation.CompilerAttachment.OriginalAlgorithm
import OptimalQLS.Preparation.CompilerAttachment.CleanState
import OptimalQLS.Preparation.CompilerAttachment.Uniformity

/-! # Strict physical preparation endpoint

A single actual local-gate list realizes the original preparation state, with
single-flag original oracle calls, separately exact query counts, constant new
scratch, explicit physical width, and its emitted elementary-gate bound.
-/
noncomputable section
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open scoped Classical
namespace OptimalQLS.Preparation.CompilerAttachment
open Matrix TransducerCompiler BinaryClock PolynomialTransform

/-- One fixed physical list works for every complete original pair of unitary
oracles and every admissible hidden scale for the supplied κ, ŝ. -/
theorem physical_preparation_complete (a n : ℕ) {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ) :
    ∃ out : Circuit a n (preparationExponent κ),
      (out.toQuery (gateEval a n _ (preparationExponent_pos h))).matrixQueries=2*mainBudget κ ∧
      (out.toQuery (gateEval a n _ (preparationExponent_pos h))).vectorQueries=2*reflectionBudget κ ŝ+1 ∧
      out.workGates ≤ 436789*(a+1)*mainBudget κ+11222*(n+1)*reflectionBudget κ ŝ+2401 ∧
      (∀ g, NamedInstruction.gate g∈out → g.arity≤2 ∧
        ∀ i j, ((gateEval a n _ (preparationExponent_pos h) g).val i j).im=0) ∧
      (∀ p adj, NamedInstruction.matrixCall p adj∈out →
        p=graphSingleFlagPort a n (preparationExponent κ)) ∧
      (∀ p adj, NamedInstruction.vectorCall p adj∈out →
        p=sourceSingleFlagPort a n (preparationExponent κ)) ∧
      (∀ (t : ℝ) (h' : BudgetParameters κ t ŝ),
        (out.workGates : ℝ)<200000000000000*κ*(a+1)+700000000000*(κ/t)*(n+1) ∧
        ∀ UA Ub, ((out.toQuery (gateEval a n _ (preparationExponent_pos h))).eval UA Ub).val *ᵥ
          Pi.single (allZero a n (preparationExponent κ)) 1=
          basisInsertion (clean a n (preparationExponent κ))*ᵥ
            originalPreparedState (fun _ : Fin a=>false) (fun _ : Fin n=>false) h' UA Ub) := by
  obtain ⟨out,hs,hm,hv,hg,_,he⟩ := physical_prepared_state a n h
  obtain ⟨hmp,hvp,hr⟩ := strictCircuit_ports out hs
  refine ⟨out,hm,hv,hg,?_,hmp,hvp,?_⟩
  · intro g hg
    exact ⟨(hr g hg).1,gate_real (preparationExponent_pos h) g (hr g hg).2⟩
  · intro t h'
    refine ⟨actual_gate_bound a n _ h' hg,?_⟩
    intro UA Ub
    rw [he UA Ub,originalPreparedState_uniform a n h h' UA Ub]

/-- Scratch cleanup is exact on every output amplitude, even though the actual
finite compiler may retain its approximate clock state. -/
theorem physical_preparation_scratch (a n : ℕ) {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ) :
    ∃ out : Circuit a n (preparationExponent κ), strictCircuit out ∧
      (out.toQuery (gateEval a n _ (preparationExponent_pos h))).matrixQueries=2*mainBudget κ ∧
      (out.toQuery (gateEval a n _ (preparationExponent_pos h))).vectorQueries=2*reflectionBudget κ ŝ+1 ∧
      (out.workGates : ℝ)<200000000000000*κ*(a+1)+700000000000*(κ/s)*(n+1) ∧
      ∀ UA Ub x scratch,
        (((out.toQuery (gateEval a n _ (preparationExponent_pos h))).eval UA Ub).val *ᵥ
          Pi.single (allZero a n (preparationExponent κ)) 1) (x,scratch)=
          if scratch=(false,false,false) then
            originalPreparedState (fun _ : Fin a=>false) (fun _ : Fin n=>false) h UA Ub x else 0 := by
  obtain ⟨out,hs,hm,hv,_,hg,he⟩ := physical_prepared_state a n h
  refine ⟨out,hs,hm,hv,hg,?_⟩
  intro UA Ub x scratch
  rw [he UA Ub,cleanVector_apply]

end OptimalQLS.Preparation.CompilerAttachment
