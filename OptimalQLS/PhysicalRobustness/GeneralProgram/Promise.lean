import OptimalQLS.PhysicalRobustness.GeneralProgram.Complete
import OptimalQLS.PhysicalRobustness.GeneralProgram.PromiseInputs

/-! Theorem 7.2 for conventional supplied physical oracles. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open scoped Classical Matrix.Norms.L2Operator
namespace OptimalQLS.PhysicalRobustness.GeneralProgram
open Matrix LowerBounds PhysicalPadding Reduction TransducerCompiler BinaryClock PolynomialTransform
open Refinement Refinement.PhysicalExecution Refinement.Repetition
variable {d : ℕ} [NeZero d] {p : QLSParameters} {δ : ℝ}

theorem promiseExecution_instrument_depth
    (I : Implementation p.signalQubits (dataQubits d) p.kappa
      (publicEstimate p.kappa p.normEstimate) p.epsilon) :
    instrumentDepth (promiseExecution I)=(promiseSyntax I).cost+1 := by
  rw [promiseSyntax_cost,promiseExecution,OracleCoordinates.program_instrumentDepth,physicalExecution_instrument_depth]

/-- The same lower-level syntax uses exactly the user's complete supplied
oracles after zero-preserving binary coordinate changes. -/
theorem promiseExecution_correct
    (I : Implementation p.signalQubits (dataQubits d) p.kappa
      (publicEstimate p.kappa p.normEstimate) p.epsilon)
    (A : Matrix (Fin d) (Fin d) ℂ) (b : DataSpace d)
    (UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × PhysicalData d) ℂ)
    (Ub : Matrix.unitaryGroup (PhysicalData d) ℂ)
    (h : PhysicalApproximateQLSPromise p δ A b UA Ub) :
    ((promiseExecution I).vectorDepth : ℝ)<216000001800000*(p.kappa/solutionScale p.alpha A b) ∧
    ((promiseSyntax I).cost : ℝ)<3000000000000000000000*p.kappa*(p.signalQubits+1)*Real.log (1/p.epsilon)+
      3000000000000000000*(p.kappa/solutionScale p.alpha A b)*(dataQubits d+1) ∧
    (2 : ℝ)/3<(promiseExecution I).successProbability UA Ub
      (basis (AdaptedExecution.initialIndex p.signalQubits (dataQubits d) (preparationExponent (2*p.kappa)))) ∧
    ∃ x : PhysicalSource d, ‖x‖=1 ∧ ‖x-physicalSolution A b‖≤p.epsilon+2*p.kappa*δ/p.alpha ∧
      (promiseExecution I).conditionalOutput UA Ub
        (basis (AdaptedExecution.initialIndex p.signalQubits (dataQubits d) (preparationExponent (2*p.kappa))))=
        pureDensity (WithLp.ofLp x) := by
  have hlo : solutionScale p.alpha A b/2≤publicEstimate p.kappa p.normEstimate := by
    rw [promise_estimate_eq h]; exact h.estimateLower
  have hhi : publicEstimate p.kappa p.normEstimate≤2*solutionScale p.alpha A b := by
    rw [promise_estimate_eq h]; exact h.estimateUpper
  have hc := physicalExecution_correct I (activeDataBits d) A h.invertible h.normBound
    (rewireUnitary (oracleRegisterCoordinates p.signalQubits d).symm UA) (promise_encoding h)
    (rewireUnitary (physicalDataCoordinates d).symm Ub) b h.unitVector (promise_source h)
    h.inverseBound h.smallError hlo hhi h.epsilonPositive h.epsilonUpper
  have hr := physicalExecution_input_resources I (activeDataBits d) A h.invertible h.normBound
    (rewireUnitary (oracleRegisterCoordinates p.signalQubits d).symm UA) (promise_encoding h)
    (rewireUnitary (physicalDataCoordinates d).symm Ub) b h.unitVector (promise_source h)
    h.inverseBound h.smallError hlo hhi h.epsilonPositive h.epsilonUpper
  simpa only [promiseExecution,OracleCoordinates.program_vectorDepth,
    OracleCoordinates.program_successProbability,OracleCoordinates.program_conditionalOutput,
    physical_solution_coordinates,promiseSyntax_cost] using And.intro hr.1 (And.intro hr.2 hc)

/-- Theorem 7.2 in the conventional input record, with the independent original
norm premise, supplied factor-two estimate, and literal input precision δ.
The witness is selected before A, b, δ, and both complete supplied oracles. -/
theorem theorem72 (p : QLSParameters) (d : ℕ) [NeZero d]
    (hk : 2≤p.kappa) (he : 0<p.epsilon) (he1 : p.epsilon<1/2) :
    ∃ I : Implementation p.signalQubits (dataQubits d) p.kappa
        (publicEstimate p.kappa p.normEstimate) p.epsilon,
      PromiseSafe I ∧ PhysicalAdapter.Safe (circuit I) ∧
      instrumentDepth (promiseExecution I)=(promiseSyntax I).cost+1 ∧
      (matrixDepth (promiseExecution I) : ℝ)<534000000000000000*p.kappa*Real.log (1/p.epsilon) ∧
      RegisterBound (2^(dataQubits d+3*p.signalQubits+2*preparationExponent (2*p.kappa)+31))
        (promiseExecution I) ∧
      dataQubits d+3*p.signalQubits+2*preparationExponent (2*p.kappa)+31≤
        dataQubits d+3*p.signalQubits+2*Nat.log2 ⌈2*p.kappa⌉₊+87 ∧
      ∀ (δ : ℝ) (A : Matrix (Fin d) (Fin d) ℂ) (b : DataSpace d)
        (UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × PhysicalData d) ℂ)
        (Ub : Matrix.unitaryGroup (PhysicalData d) ℂ),
        PhysicalApproximateQLSPromise p δ A b UA Ub →
        ((promiseExecution I).vectorDepth : ℝ)<216000001800000*(p.kappa/solutionScale p.alpha A b) ∧
        ((promiseSyntax I).cost : ℝ)<3000000000000000000000*p.kappa*(p.signalQubits+1)*Real.log (1/p.epsilon)+
          3000000000000000000*(p.kappa/solutionScale p.alpha A b)*(dataQubits d+1) ∧
        (2 : ℝ)/3<(promiseExecution I).successProbability UA Ub
          (basis (AdaptedExecution.initialIndex p.signalQubits (dataQubits d) (preparationExponent (2*p.kappa)))) ∧
        ∃ x : PhysicalSource d, ‖x‖=1 ∧ ‖x-physicalSolution A b‖≤p.epsilon+2*p.kappa*δ/p.alpha ∧
          (promiseExecution I).conditionalOutput UA Ub
            (basis (AdaptedExecution.initialIndex p.signalQubits (dataQubits d) (preparationExponent (2*p.kappa))))=
            pureDensity (WithLp.ofLp x) := by
  obtain ⟨hlo,hhi⟩ := publicEstimate_bounds (ŝ := p.normEstimate) hk
  obtain ⟨I⟩ := PhysicalRobustness.PhysicalProgram.implementation_exists
    p.signalQubits (dataQubits d+1) hk hlo hhi he he1
  refine ⟨I,promise_safe I,circuit_safe I,promiseExecution_instrument_depth I,?_,?_,(physicalExecution_width_bound I).2,?_⟩
  · simpa only [promiseExecution,OracleCoordinates.program_matrixDepth] using physicalExecution_matrix_bound I he he1
  · exact (OracleCoordinates.program_registerBound _ _ _ _).mpr (physicalExecution_width_bound I).1
  · intro δ A b UA Ub hp
    exact promiseExecution_correct I A b UA Ub hp

end OptimalQLS.PhysicalRobustness.GeneralProgram
