import OptimalQLS.Reduction.GenericSolver.FreshCopiesPool
import OptimalQLS.Reduction.GenericSolver.FreshCopiesHeadFinite
import OptimalQLS.Reduction.GenericSolver.BranchwiseRepetition

/-! Probability and actual-terminal accuracy of the same fully physical fresh
process. The output may be a branch-dependent mixture of close pure states. -/
noncomputable section
open scoped Classical BigOperators
namespace OptimalQLS.Reduction.GenericSolver.FreshCopies
open Matrix LowerBounds Refinement.Repetition TransducerCompiler BinaryClock
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
variable {A B VA VB : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable {argumentsA : A ≃ (VA → Bool)} {argumentsB : B ≃ (VB → Bool)}

theorem freshProcess_step (n : ℕ) (R : Register)
    (p : Process argumentsA argumentsB (doubledRegister n) R)
    (zero : R.State) (out : Bits n) (k : ℕ) (UA : Matrix.unitaryGroup A ℂ)
    (Ub : Matrix.unitaryGroup B ℂ) (select : Bool → Bool) :
    (freshProcess n R p (k+1)).lower.executeDensity UA Ub select (poolBasis R n zero out (k+1))=
      (if select true then attemptDensity p.lower (extractRightEmbedding (doubledIndex n))
        (R.index zero) UA Ub else 0)+
      (1-attemptMass p.lower (extractRightEmbedding (doubledIndex n)) (R.index zero) UA Ub) •
        (freshProcess n R p k).lower.executeDensity UA Ub select (poolBasis R n zero out k) := by
  let T:=poolRegister R n k
  let next:=freshProcess n R p k
  let z:=poolBasis R n zero out k
  let e:=extractRightEmbedding (doubledIndex n)
  let rho:=next.lower.executeDensity UA Ub select z
  let L:=fun flag:Bool=>if flag then acceptedContinuationDensity e select rho else resetDensity rho
  let cont:=fun flag:Bool=>if flag then headProcess n T next
    else Process.trace (discardFirstLayout (doubledRegister n) T) next
  have hz:bornMass z=1:=poolBasis_bornMass R n zero out k
  have hL:∀flag v,(cont flag).lower.executeDensity UA Ub select (tensorVector v z)=L flag (pureDensity v) := by
    intro flag v
    cases flag <;> cases hs:select true <;>
      simp [cont,L,rho,headProcess_density,traceFirst_density,resetDensity,
        acceptedContinuationDensity,extractDensity_pure,traceReal,←bornMass_eq_trace,hs,hz,e]
  rw [freshProcess,poolBasis_succ,Process.tensor_bind_density T p cont UA Ub select L z hL]
  have ht:=program_total_trace p.lower UA Ub (basis (R.index zero))
  rw [basis_bornMass] at ht
  simp only [L,Bool.true_eq,ite_true,Bool.false_eq_true,ite_false,
    acceptedContinuationDensity,resetDensity,LinearMap.add_apply,
    LinearMap.smulRight_apply,LinearMap.sub_apply,LinearMap.comp_apply]
  simp only [traceReal,LinearMap.coe_mk,AddHom.coe_mk]
  change _=(if select true then extractDensity e (p.lower.executeDensity UA Ub id (basis (R.index zero))) else 0)+
    (1-(extractDensity e (p.lower.executeDensity UA Ub id (basis (R.index zero)))).trace.re) • rho
  split_ifs
  · rw [add_assoc,←add_smul]
    congr 1
    congr 1
    linarith
  · simp only [LinearMap.zero_apply,zero_add]
    rw [←add_smul]
    congr 1
    linarith

theorem freshProcess_density_refines (n : ℕ) (R : Register)
    (p : Process argumentsA argumentsB (doubledRegister n) R)
    (zero : R.State) (out : Bits n) (k : ℕ) (UA : Matrix.unitaryGroup A ℂ)
    (Ub : Matrix.unitaryGroup B ℂ) (select : Bool → Bool) :
    (freshProcess n R p k).lower.executeDensity UA Ub select (poolBasis R n zero out k)=
      (retrySolver p.lower (extractRightEmbedding (doubledIndex n)) (R.index zero)
        ((dataRegister n).index out) k).executeDensity UA Ub select (basis (R.index zero)) := by
  induction k with
  | zero =>
    simp [freshProcess,Process.lower,poolBasis_zero,retrySolver,failureOutput_executeDensity,
      basis_bornMass,FiniteOracleProgram.executeDensity]
  | succ k ih => rw [freshProcess_step,retrySolver_step,ih]

theorem freshProcess_branchwise (n : ℕ) (R : Register)
    (p : Process argumentsA argumentsB (doubledRegister n) R) (zero : R.State) (out : Bits n)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (x : EuclideanSpace ℂ (Fin (dataRegister n).dimension)) {ε : ℝ}
    (hx : ‖x‖=1) (hε0 : 0<ε) (hε1 : ε<1/2)
    (h : Returns (CloseDoubledState (doubledIndex n) x ε) UA Ub p.lower (basis (R.index zero))) (k : ℕ) :
    Returns (CloseState x ε) UA Ub (freshProcess n R p k).lower (poolBasis R n zero out k) := by
  have hP:∀v (c:ℂ),CloseState x ε v→CloseState x ε (c • v):=fun _ c hv=>hv.smul c
  induction k with
  | zero => intro hf;contradiction
  | succ k ih =>
    rw [freshProcess,poolBasis_succ]
    apply Process.tensor_bind_returns (poolRegister R n k) (CloseState x ε)
      (CloseDoubledState (doubledIndex n) x ε) p _ UA Ub _ _ h
    intro flag v hv
    cases flag
    · exact traceFirst_returns (doubledRegister n) (poolRegister R n k) (dataRegister n)
        (freshProcess n R p k) _ hP UA Ub v _ ih
    · exact headProcess_returns n (poolRegister R n k) (freshProcess n R p k)
        _ hP UA Ub v _
        (extract_closeDoubledState (doubledIndex n) x hx hε0 hε1 v (hv rfl)).1 ih

/-- The physical tree simultaneously carries the actual source-query, unitary
cost, measurement and width bounds, and the branchwise output guarantee. -/
theorem fresh_three_physical (n : ℕ) (R : Register)
    (p : Process argumentsA argumentsB (doubledRegister n) R) (zero : R.State) (out : Bits n)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (x : EuclideanSpace ℂ (Fin (dataRegister n).dimension)) {ε : ℝ}
    (hx : ‖x‖=1) (hε0 : 0<ε) (hε1 : ε<1/2)
    (h : Returns (CloseDoubledState (doubledIndex n) x ε) UA Ub p.lower (basis (R.index zero)))
    (hp : 2/3≤p.lower.successProbability UA Ub (basis (R.index zero))) :
    let result:=freshProcess n R p 3
    (2:ℝ)/3<result.lower.successProbability UA Ub (poolBasis R n zero out 3) ∧
    (∀ t : result.lower.Terminal,result.lower.terminalSuccess t=true→
      CloseState x ε ((result.lower.terminalPath (.initial (poolBasis R n zero out 3)) t).state UA Ub)) ∧
    result.work≤3*p.work ∧ result.measurements≤3*(p.measurements+1) ∧
    Refinement.Repetition.matrixDepth result.lower≤3*p.matrixCalls ∧
    result.lower.vectorDepth≤3*p.vectorCalls ∧
    Refinement.Repetition.RegisterBound (2^(4*R.qubits)) result.lower := by
  dsimp only
  refine ⟨?_,?_,(freshProcess_resources n R p 3).1,(freshProcess_resources n R p 3).2.1,
    (freshProcess_query_depths n R p 3).1,(freshProcess_query_depths n R p 3).2,
    fresh_three_registerBound n R p⟩
  · have hs:=(proposition23_branchwise p.lower (doubledIndex n) (R.index zero)
      ((dataRegister n).index out) UA Ub x hx hε0 hε1 h hp).1
    simpa only [FiniteOracleProgram.successProbability,freshProcess_density_refines] using hs
  · exact (returns_iff_terminal _ _ (.initial (poolBasis R n zero out 3)) UA Ub).mp
      (freshProcess_branchwise n R p zero out UA Ub x hx hε0 hε1 h 3)

end OptimalQLS.Reduction.GenericSolver.FreshCopies
