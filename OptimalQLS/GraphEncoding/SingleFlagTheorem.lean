import OptimalQLS.GraphEncoding.GraphFlagAdapter
import OptimalQLS.GraphEncoding.SafeRefinement

/-! # Full allowed graph calls with only singly controlled original oracles -/
noncomputable section
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 1000000
namespace OptimalQLS.GraphEncoding
open Matrix PolynomialTransform DirtyAncilla
variable {S D B : Type*} [Fintype S] [DecidableEq S]
  [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

/-- The strongest allowed-call endpoint: all work gates are genuinely real
one- and two-qubit instructions, every emitted original-oracle call has exactly
one named flag control, and the shared three-bit scratch returns to zero. -/
theorem controlled_graph_single_flag (κ : ℝ) (hκ : 0 < κ) (mask : Bool × Bool) :
    ∃ c : ElementaryCircuit (S × D) B ControlledGraphWire (S × D),
      c.toQuery.matrixQueries=2 ∧ c.toQuery.vectorQueries=0 ∧ c.workGates ≤ 252304 ∧
      SingleFlagRealCircuit flagWire c ∧
      ∀ (adj : Bool) (U : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ),
        (c.toQuery.eval U Ub).val * basisInsertion (graphLocalClean (S := S) (D := D)) =
          basisInsertion (graphLocalClean (S := S) (D := D)) *
            ((maskedGraphPort (PhysicalSignal S × (Fin 4 × D)) mask).apply
              (if adj then (physicalEncoding κ hκ U)⁻¹ else physicalEncoding κ hκ U)).val := by
  let J := basisInsertion (graphLocalClean (S := S) (D := D))
  have hw : ∀ U, QueryInstruction.work U ∈ allowedGraphCall S D B κ hκ mask false →
      ∃ code : ElementaryCircuit (S × D) B ControlledGraphWire (S × D),
        code.toQuery.matrixQueries=0 ∧ code.toQuery.vectorQueries=0 ∧ code.workGates≤3214 ∧
        SingleFlagRealCircuit flagWire code ∧ ∀ UA Ub, (code.toQuery.eval UA Ub).val*J=J*U.val := by
    intro U hU
    obtain ⟨q,hq,hEq⟩ := List.mem_map.mp hU
    cases q with
    | matrixCall p b => cases hEq
    | vectorCall p b => cases hEq
    | work V =>
      have hv : (maskedGraphPort (PhysicalSignal S × (Fin 4 × D)) mask).apply V = U :=
        QueryInstruction.work.inj hEq
      obtain ⟨g,hg,ha⟩ := elementaryGraph_work_elementary κ hκ V hq
      refine ⟨elementaryMacro (g.controlledCode mask), (elementaryMacro_queries _).1,
        (elementaryMacro_queries _).2, ?_, ?_, ?_⟩
      · simpa using g.controlledCode_length mask
      · exact elementaryMacro_safe _ _ (fun p hp => (g.controlledCode_real mask p hp).1)
      · intro UA Ub
        rw [elementaryMacro_eval,← hv,← hg]
        exact g.controlledCode_intertwines mask
  have hq : ∀ p adj, QueryInstruction.matrixCall p adj ∈ allowedGraphCall S D B κ hκ mask false →
      ∃ code : ElementaryCircuit (S × D) B ControlledGraphWire (S × D),
        code.toQuery.matrixQueries=1 ∧ code.toQuery.vectorQueries=0 ∧ code.workGates≤4020 ∧
        SingleFlagRealCircuit flagWire code ∧ ∀ UA Ub, (code.toQuery.eval UA Ub).val*J=
          J*(p.apply (if adj then UA⁻¹ else UA)).val := by
    intro p adj hp
    refine ⟨graphFlagOracleCircuit mask adj, (graphFlagOracleCircuit_counts _ _).1,
      (graphFlagOracleCircuit_counts _ _).2.1, (graphFlagOracleCircuit_counts _ _).2.2, ?_, ?_⟩
    · exact maskedOracleCircuit_safe _ _ _ _ _
    · intro UA Ub
      rw [allowedGraph_query_port κ hκ mask p adj hp,QueryPort.comp_apply]
      exact graphFlagOracleCircuit_intertwines mask adj UA Ub
  obtain ⟨c,hcm,hcv,hcg,hcs,hce⟩ := refine_real_single_flag
    (allowedGraphCall S D B κ hκ mask false) (allowedGraphCall_queries κ hκ mask false).2
    J flagWire 3214 4020 hw hq
  refine ⟨c,hcm.trans (allowedGraphCall_queries κ hκ mask false).1,hcv,?_,hcs,?_⟩
  · have hn : workInstructions (allowedGraphCall S D B κ hκ mask false)=76 := by
      simp only [allowedGraphCall,workInstructions_lift,(elementaryGraphCircuit_counts κ hκ).2.2]
    rw [hn,(allowedGraphCall_queries κ hκ mask false).1] at hcg
    exact hcg
  · intro adj U Ub
    have hi : (physicalEncoding κ hκ U)⁻¹=physicalEncoding κ hκ U := by
      apply Subtype.ext
      exact physicalEncoding_hermitian κ hκ U
    have hh := hce U Ub
    rw [allowedGraphCall_eval] at hh
    cases adj <;> simpa [hi] using hh

end OptimalQLS.GraphEncoding
