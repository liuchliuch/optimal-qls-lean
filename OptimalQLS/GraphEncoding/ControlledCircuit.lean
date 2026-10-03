import OptimalQLS.GraphEncoding.ControlledIntertwining
import OptimalQLS.PolynomialTransform.ElementaryCircuit

/-! # Allowed masked graph calls: actual elementary lists and original oracle accounting -/
noncomputable section
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 1000000
namespace OptimalQLS.GraphEncoding
open Matrix PolynomialTransform TransducerCompiler DirtyAncilla
variable {S D B : Type*} [Fintype S] [DecidableEq S]
  [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

/-- Full Proposition4.3 allowed-call realization, with the two exact QSVT mask
controls. The same three scratch bits return to zero after every call. -/
theorem controlled_graph_elementary (κ : ℝ) (hκ : 0 < κ) (mask : Bool × Bool) :
    ∃ c : ElementaryCircuit (S × D) B ControlledGraphWire (S × D),
      c.toQuery.matrixQueries=2 ∧ c.toQuery.vectorQueries=0 ∧ c.workGates ≤ 244264 ∧
      ∀ (U : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ),
        (c.toQuery.eval U Ub).val * basisInsertion (graphLocalClean (S := S) (D := D)) =
          basisInsertion (graphLocalClean (S := S) (D := D)) *
            ((maskedGraphPort (PhysicalSignal S × (Fin 4 × D)) mask).apply
              (physicalEncoding κ hκ U)).val := by
  let e := (graphLocalWiring S D).symm
  let J := basisInsertion (graphLocalClean (S := S) (D := D))
  let port := scratchPort e
  have hp (U : Matrix.unitaryGroup ((Bool × Bool) × (PhysicalSignal S × (Fin 4 × D))) ℂ) :
      (port.apply U).val * J = J * U.val := by
    exact scratchPort_intertwines e (false,false,false) U
  have hw : ∀ U, QueryInstruction.work U ∈ allowedGraphCall S D B κ hκ mask false →
      ∃ code : List (PhaseGate ControlledGraphWire), code.length ≤ 3214 ∧
        (elementaryPlacement (D := S × D) (phaseEval code)).val * J = J * U.val := by
    intro U hU
    obtain ⟨q,hq,hEq⟩ := List.mem_map.mp hU
    cases q with
    | matrixCall p b => cases hEq
    | vectorCall p b => cases hEq
    | work V =>
      have hv : (maskedGraphPort (PhysicalSignal S × (Fin 4 × D)) mask).apply V = U := by
        exact QueryInstruction.work.inj hEq
      obtain ⟨g,hg,ha⟩ := elementaryGraph_work_elementary κ hκ V hq
      refine ⟨g.controlledCode mask, g.controlledCode_length mask, ?_⟩
      rw [← hv, ← hg]
      exact g.controlledCode_intertwines mask
  obtain ⟨c,hq,hv,hg,he⟩ := refine_query_circuit (allowedGraphCall S D B κ hκ mask false)
    J port hp 3214 hw
  refine ⟨c,?_,?_,?_,?_⟩
  · exact hq.trans (allowedGraphCall_queries κ hκ mask false).1
  · exact hv.trans (allowedGraphCall_queries κ hκ mask false).2
  · have hc : workInstructions (allowedGraphCall S D B κ hκ mask false)=76 := by
      simp only [allowedGraphCall,workInstructions_lift,(elementaryGraphCircuit_counts κ hκ).2.2]
    rw [hc] at hg
    exact hg
  · intro U Ub
    simpa only [allowedGraphCall_eval, Bool.false_eq_true, ite_false] using he U Ub

/-- The same physical call covers adjoints, with unchanged original-query and
real elementary-work bounds, because the entire graph oracle is Hermitian. -/
theorem controlled_graph_elementary_adjoint (κ : ℝ) (hκ : 0 < κ) (mask : Bool × Bool) :
    ∃ c : ElementaryCircuit (S × D) B ControlledGraphWire (S × D),
      c.toQuery.matrixQueries=2 ∧ c.toQuery.vectorQueries=0 ∧ c.workGates ≤ 244264 ∧
      ∀ (adj : Bool) (U : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ),
        (c.toQuery.eval U Ub).val * basisInsertion (graphLocalClean (S := S) (D := D)) =
          basisInsertion (graphLocalClean (S := S) (D := D)) *
            ((maskedGraphPort (PhysicalSignal S × (Fin 4 × D)) mask).apply
              (if adj then (physicalEncoding κ hκ U)⁻¹ else physicalEncoding κ hκ U)).val := by
  obtain ⟨c,hq,hv,hg,he⟩ := controlled_graph_elementary (S := S) (D := D) (B := B) κ hκ mask
  refine ⟨c,hq,hv,hg,?_⟩
  intro adj U Ub
  have hi : (physicalEncoding κ hκ U)⁻¹ = physicalEncoding κ hκ U := by
    apply Subtype.ext
    exact physicalEncoding_hermitian κ hκ U
  cases adj <;> simpa [hi] using he U Ub

end OptimalQLS.GraphEncoding
