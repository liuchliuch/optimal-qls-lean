import OptimalQLS.Reduction.PublicInputs

/-! # One original-input program selected before every supplied oracle and state -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
open scoped Classical Matrix.Norms.L2Operator
namespace OptimalQLS.Reduction.PhysicalUpper
open Matrix LowerBounds PhysicalPadding TransducerCompiler BinaryClock PolynomialTransform
open Refinement Refinement.PhysicalExecution Refinement.Repetition Preparation PublicInputs
attribute [local irreducible] CostedExecution.repeated CostedExecution.Program.lower Repetition.repeatProgram

def publicBudget (p : QLSParameters) (hκ : 2≤p.kappa) :
    BudgetParameters p.kappa (knownScaleWitness p.kappa (effectiveEstimate p.kappa p.normEstimate))
      (effectiveEstimate p.kappa p.normEstimate) :=
  knownScaleWitness_budget hκ (effectiveEstimate_bounds hκ).1 (effectiveEstimate_bounds hκ).2

abbrev Implementation (p : QLSParameters) (d : ℕ) (hκ : 2≤p.kappa) :=
  PhysicalProgram.Implementation p.signalQubits (dataQubits d+1) (ε := p.epsilon) (publicBudget p hκ)

def promiseExecution {p : QLSParameters} {d : ℕ} {hκ : 2≤p.kappa} (I : Implementation p d hκ) :=
  OracleCoordinates.program (oracleRegisterCoordinates p.signalQubits d) (physicalDataCoordinates d)
    (DirectCosted.algorithm I)

def initialIndex (p : QLSParameters) (d : ℕ) :=
  AdaptedExecution.initialIndex p.signalQubits (dataQubits d) (preparationExponent p.kappa)

theorem promise_matrix_bound {p : QLSParameters} {d : ℕ} {hκ : 2≤p.kappa}
    (I : Implementation p d hκ) (hε0 : 0<p.epsilon) (hε1 : p.epsilon<1/2) :
    (matrixDepth (promiseExecution I) : ℝ)<1320000000000000*p.kappa*Real.log (1/p.epsilon) := by
  rw [promiseExecution,OracleCoordinates.program_matrixDepth]
  exact DirectCosted.matrix_bound I hε0 hε1

theorem promise_register_bound {p : QLSParameters} {d : ℕ} {hκ : 2≤p.kappa}
    (I : Implementation p d hκ) :
    RegisterBound (2^(dataQubits d+3*p.signalQubits+2*preparationExponent p.kappa+31))
      (promiseExecution I) ∧
    dataQubits d+3*p.signalQubits+2*preparationExponent p.kappa+31≤
      dataQubits d+3*p.signalQubits+2*Nat.log2 ⌈p.kappa⌉₊+87 := by
  have hw := DirectCosted.width_bound I
  exact ⟨(OracleCoordinates.program_registerBound _ _ _ _).mpr hw.1,hw.2⟩

theorem promise_correct {p : QLSParameters} {d : ℕ} [NeZero d] {hκ : 2≤p.kappa}
    (I : Implementation p d hκ)
    (A : Matrix (Fin d) (Fin d) ℂ) (b : DataSpace d)
    (UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × PhysicalData d) ℂ)
    (Ub : Matrix.unitaryGroup (PhysicalData d) ℂ)
    (hp : PhysicalRelaxedQLSPromise p A b UA Ub) :
    ((promiseExecution I).vectorDepth : ℝ)<72000000600000*(p.kappa/solutionScale p.alpha A b) ∧
    ((DirectCosted.algorithmSyntax I).cost : ℝ)<
      300000000000000000000*p.kappa*(p.signalQubits+1)*Real.log (1/p.epsilon)+
      1000000000000000000*(p.kappa/solutionScale p.alpha A b)*(dataQubits d+1) ∧
    (2 : ℝ)/3<(promiseExecution I).successProbability UA Ub (basis (initialIndex p d)) ∧
    ∃ x : PhysicalSource d, ‖x‖=1 ∧ ‖x-physicalSolution A b‖≤p.epsilon ∧
      (promiseExecution I).conditionalOutput UA Ub (basis (initialIndex p d))=
        pureDensity (WithLp.ofLp x) := by
  have hlo : 3*solutionScale p.alpha A b/8≤effectiveEstimate p.kappa p.normEstimate := by
    rw [promise_estimate_eq hp]
    exact hp.estimateLower
  have hhi : effectiveEstimate p.kappa p.normEstimate≤5*solutionScale p.alpha A b/2 := by
    rw [promise_estimate_eq hp]
    exact hp.estimateUpper
  have hc := DirectCosted.algorithm_correct I (activeDataBits d) A hp.invertible b hp.unitVector
    (rewireUnitary (oracleRegisterCoordinates p.signalQubits d).symm UA) (promise_encoding hp)
    (rewireUnitary (physicalDataCoordinates d).symm Ub) (promise_source hp)
    hp.inverseBound hlo hhi hp.epsilonPositive hp.epsilonUpper
  have hr := DirectCosted.algorithm_input_resources I (activeDataBits d) A hp.invertible b hp.unitVector
    (rewireUnitary (oracleRegisterCoordinates p.signalQubits d).symm UA) (promise_encoding hp)
    (rewireUnitary (physicalDataCoordinates d).symm Ub) (promise_source hp)
    hp.inverseBound hlo hhi hp.epsilonPositive hp.epsilonUpper
  refine ⟨?_,hr.2,?_,?_⟩
  · simpa only [promiseExecution,OracleCoordinates.program_vectorDepth] using hr.1
  · simpa only [promiseExecution,OracleCoordinates.program_successProbability,initialIndex] using hc.1
  · simpa only [promiseExecution,OracleCoordinates.program_conditionalOutput,initialIndex,
      physical_solution_coordinates] using hc.2

/-- The witness is chosen solely from the public classical parameters. Actual
solution norms, matrices, vector states and complete oracle extensions occur
only after it. Both the factor-two and relaxed source promises are supported. -/
theorem physical_upper_witness (p : QLSParameters) (d : ℕ) [NeZero d]
    (hκ : 2≤p.kappa) (hε0 : 0<p.epsilon) (hε1 : p.epsilon<1/2) :
    ∃ I : Implementation p d hκ,
      (matrixDepth (promiseExecution I) : ℝ)<1320000000000000*p.kappa*Real.log (1/p.epsilon) ∧
      RegisterBound (2^(dataQubits d+3*p.signalQubits+2*preparationExponent p.kappa+31)) (promiseExecution I) ∧
      dataQubits d+3*p.signalQubits+2*preparationExponent p.kappa+31≤
        dataQubits d+3*p.signalQubits+2*Nat.log2 ⌈p.kappa⌉₊+87 ∧
      ∀ (A : Matrix (Fin d) (Fin d) ℂ) (b : DataSpace d)
        (UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × PhysicalData d) ℂ)
        (Ub : Matrix.unitaryGroup (PhysicalData d) ℂ),
        PhysicalRelaxedQLSPromise p A b UA Ub →
        ((promiseExecution I).vectorDepth : ℝ)<72000000600000*(p.kappa/solutionScale p.alpha A b) ∧
        ((DirectCosted.algorithmSyntax I).cost : ℝ)<
          300000000000000000000*p.kappa*(p.signalQubits+1)*Real.log (1/p.epsilon)+
          1000000000000000000*(p.kappa/solutionScale p.alpha A b)*(dataQubits d+1) ∧
        (2 : ℝ)/3<(promiseExecution I).successProbability UA Ub (basis (initialIndex p d)) ∧
        ∃ x : PhysicalSource d, ‖x‖=1 ∧ ‖x-physicalSolution A b‖≤p.epsilon ∧
          (promiseExecution I).conditionalOutput UA Ub (basis (initialIndex p d))=
            pureDensity (WithLp.ofLp x) := by
  obtain ⟨I⟩ := PhysicalProgram.implementation_exists p.signalQubits (dataQubits d+1)
    (publicBudget p hκ) hε0 hε1
  have hw := promise_register_bound (hκ := hκ) I
  exact ⟨I,promise_matrix_bound (hκ := hκ) I hε0 hε1,hw.1,hw.2,
    fun A b UA Ub hp=>promise_correct (hκ := hκ) I A b UA Ub hp⟩

end OptimalQLS.Reduction.PhysicalUpper
