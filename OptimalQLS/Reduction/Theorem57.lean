import OptimalQLS.Reduction.PhysicalUpperResources
import OptimalQLS.Reduction.DirectSafety

/-! # Theorem 5.7 in the full supplied physical two-oracle model

The physical implementation directly accepts the dilation head together with
the auxiliary pattern and repeats that attempt a fixed number of times.
Proposition 2.3's separate three-retry implementation is proved independently.
-/
noncomputable section
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
open scoped Classical Matrix.Norms.L2Operator
namespace OptimalQLS.Reduction.PhysicalUpper
open Matrix LowerBounds PhysicalPadding TransducerCompiler BinaryClock PolynomialTransform
open Refinement Repetition CostedExecution
variable {p : QLSParameters} {d : ℕ} {hκ : 2≤p.kappa}
attribute [local irreducible] repeated CostedExecution.Program.lower repeatProgram

def PhysicallySafe (I : Implementation p d hκ) : Prop :=
  DirectCosted.CoordinateSafety (PhysicalAdapter.adapted I)
    (Preparation.CompilerAttachment.preparationExponent_pos (publicBudget p hκ)) 600000
    (oracleRegisterCoordinates p.signalQubits d) (physicalDataCoordinates d)

theorem promise_physically_safe (I : Implementation p d hκ) : PhysicallySafe I :=
  DirectCosted.sourceSyntax_safe _ _ _ (PhysicalAdapter.adapted_safe I) _ _

def InputGuarantee (I : Implementation p d hκ) (A : Matrix (Fin d) (Fin d) ℂ) (b : DataSpace d)
    (UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × PhysicalData d) ℂ)
    (Ub : Matrix.unitaryGroup (PhysicalData d) ℂ) : Prop :=
  ((promiseExecution I).vectorDepth : ℝ)<72000000600000*(p.kappa/solutionScale p.alpha A b) ∧
  ((promiseSyntax I).cost : ℝ)<
    300000000000000000000*p.kappa*(p.signalQubits+1)*Real.log (1/p.epsilon)+
    1000000000000000000*(p.kappa/solutionScale p.alpha A b)*(dataQubits d+1) ∧
  (2 : ℝ)/3<(promiseExecution I).successProbability UA Ub (basis (initialIndex p d)) ∧
  ∃ x : PhysicalSource d, ‖x‖=1 ∧ ‖x-physicalSolution A b‖≤p.epsilon ∧
    (promiseExecution I).conditionalOutput UA Ub (basis (initialIndex p d))=pureDensity (WithLp.ofLp x)

def UniformRelaxedGuarantee (I : Implementation p d hκ) : Prop :=
  ∀ (A : Matrix (Fin d) (Fin d) ℂ) (b : DataSpace d)
    (UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × PhysicalData d) ℂ)
    (Ub : Matrix.unitaryGroup (PhysicalData d) ℂ),
    PhysicalRelaxedQLSPromise p A b UA Ub → InputGuarantee I A b UA Ub

def UniformExactGuarantee (I : Implementation p d hκ) : Prop :=
  ∀ (A : Matrix (Fin d) (Fin d) ℂ) (b : DataSpace d)
    (UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × PhysicalData d) ℂ)
    (Ub : Matrix.unitaryGroup (PhysicalData d) ℂ),
    PhysicalExactQLSPromise p A b UA Ub → InputGuarantee I A b UA Ub

/-- Includes the explicitly relaxed estimate of the manuscript. Every gate,
measurement, reset and original-oracle argument wire belongs to this witness. -/
theorem theorem57_relaxed (p : QLSParameters) (d : ℕ) [NeZero d]
    (hκ : 2≤p.kappa) (hε0 : 0<p.epsilon) (hε1 : p.epsilon<1/2) :
    ∃ I : Implementation p d hκ,
      PhysicallySafe I ∧
      instrumentDepth (promiseExecution I)=(promiseSyntax I).cost+1 ∧
      (matrixDepth (promiseExecution I) : ℝ)<1320000000000000*p.kappa*Real.log (1/p.epsilon) ∧
      RegisterBound (2^(dataQubits d+3*p.signalQubits+2*preparationExponent p.kappa+31)) (promiseExecution I) ∧
      dataQubits d+3*p.signalQubits+2*preparationExponent p.kappa+31≤
        dataQubits d+3*p.signalQubits+2*Nat.log2 ⌈p.kappa⌉₊+87 ∧
      UniformRelaxedGuarantee I := by
  obtain ⟨I,hq,hr,hw,hcorrect⟩ := physical_upper_witness p d hκ hε0 hε1
  refine ⟨I,promise_physically_safe I,promise_instrument_depth I,hq,hr,hw,?_⟩
  intro A b UA Ub hp
  have hh := hcorrect A b UA Ub hp
  simpa only [InputGuarantee,promiseSyntax_cost] using hh

/-- **Theorem 5.7.** The original factor-two supplied estimate is retained,
and the same chosen program handles every full oracle extension permitted by
the physical input promise. All bounds refer to that program and its exact
primitive syntax, with no oracle-dependent choice of code. -/
theorem theorem57 (p : QLSParameters) (d : ℕ) [NeZero d]
    (hκ : 2≤p.kappa) (hε0 : 0<p.epsilon) (hε1 : p.epsilon<1/2) :
    ∃ I : Implementation p d hκ,
      PhysicallySafe I ∧
      instrumentDepth (promiseExecution I)=(promiseSyntax I).cost+1 ∧
      (matrixDepth (promiseExecution I) : ℝ)<1320000000000000*p.kappa*Real.log (1/p.epsilon) ∧
      RegisterBound (2^(dataQubits d+3*p.signalQubits+2*preparationExponent p.kappa+31)) (promiseExecution I) ∧
      dataQubits d+3*p.signalQubits+2*preparationExponent p.kappa+31≤
        dataQubits d+3*p.signalQubits+2*Nat.log2 ⌈p.kappa⌉₊+87 ∧
      UniformExactGuarantee I := by
  obtain ⟨I,hphys,hi,hq,hr,hw,hcorrect⟩ := theorem57_relaxed p d hκ hε0 hε1
  exact ⟨I,hphys,hi,hq,hr,hw,fun A b UA Ub hp=>hcorrect A b UA Ub hp.toRelaxed⟩

end OptimalQLS.Reduction.PhysicalUpper
