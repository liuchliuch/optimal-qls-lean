import OptimalQLS.Reduction.GenericSolver.FreshCopiesPhysicalCorrectness
import OptimalQLS.Reduction.GenericSolver.FreshCopiesEmbed
import OptimalQLS.Reduction.GenericSolver.PhysicalNormalizeComplete
import OptimalQLS.Reduction.GenericSolver.BranchwiseSource

/-! The actual original-oracle reduction for an arbitrary supplied physical
solver, including ordinary calls, branching and mixed successful ensembles. -/
noncomputable section
open scoped Classical
namespace OptimalQLS.Reduction.GenericSolver.FreshCopies
open Matrix LowerBounds Refinement.Repetition TransducerCompiler BinaryClock PolynomialTransform
open Refinement.CostedExecution Physical
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
variable {P W : Type} [Fintype P] [DecidableEq P] [Fintype W] [DecidableEq W]
variable {chart : P ≃ (W → Bool)} {a n : ℕ}

def adaptedRegister (chart : P ≃ (W → Bool)) : Register :=
  Register.ofChart (Physical.coordinates (enableCoordinates chart))

def adaptedZero (zero : P) : (adaptedRegister chart).State := ((false,zero),(false,false,false))

def adaptedProcess (F : OutputLayout chart n) (c : AnyProgram chart a n) :
    Process (matrixArguments a n) (Equiv.refl (Bits n)) (doubledRegister n) (adaptedRegister chart) :=
  (c.adapt F).toProcess gateEval (matrixArguments a n) (Equiv.refl (Bits n)) (c.adapt_safe F)

theorem adaptedProcess_lower (F : OutputLayout chart n) (c : AnyProgram chart a n) :
    (adaptedProcess F c).lower=(c.adapt F).lower gateEval :=
  PhysicalProgram.toProcess_lower _ _ _ _ _

theorem adaptedProcess_resources (F : OutputLayout chart n) (c : AnyProgram chart a n) :
    (adaptedProcess F c).work≤c.work+4802*c.matrixCalls+c.vectorCalls ∧
    (adaptedProcess F c).matrixCalls=2*c.matrixCalls ∧
    (adaptedProcess F c).vectorCalls=c.vectorCalls ∧
    (adaptedProcess F c).measurements=c.measurements := by
  have he:=PhysicalProgram.toProcess_resources gateEval (matrixArguments a n) (Equiv.refl (Bits n))
    (c.adapt F) (c.adapt_safe F)
  have hc:=c.adapt_resources F
  exact ⟨he.1.le.trans hc.1,he.2.2.1.trans hc.2.1,he.2.2.2.trans hc.2.2.1,he.2.1.trans hc.2.2.2⟩

theorem adaptedRegister_qubits : (adaptedRegister chart).qubits=Fintype.card W+4 := by
  simp [adaptedRegister,Register.ofChart,Register.qubits,Physical.ScratchWire]
  omega

theorem indexedVector_single (R : Register) (zero : R.State) :
    indexedVector R (Pi.single zero (1:ℂ))=basis (R.index zero) := by
  ext i
  have he:R.index.symm i=zero ↔ i=R.index zero := by
    constructor
    · intro h
      have hh:=congrArg R.index h
      rw [Equiv.apply_symm_apply] at hh
      exact hh
    · intro h;rw [h,Equiv.symm_apply_apply]
  simp only [indexedVector,Function.comp_apply,Pi.single_apply,basis,he]

theorem finiteVector_single (chart : P ≃ (W → Bool)) (zero : P) :
    finiteVector (Pi.single zero (1:ℂ))=basis ((Fintype.equivFin P) zero) :=
  indexedVector_single (Register.ofChart chart) zero

theorem initialState_single (zero : P) :
    AnyProgram.initialState (Pi.single zero (1:ℂ))=Pi.single (adaptedZero (chart := chart) zero) 1 := by
  change basisInsertion (fun q:Bool×P=>(q,(false,false,false)))*ᵥ
    (basisInsertion (fun p:P=>(false,p))*ᵥPi.single zero (1:ℂ))=_
  rw [basisInsertion_basis,basisInsertion_basis]
  rfl

theorem adaptedProcess_density (F : OutputLayout chart n) (c : AnyProgram chart a n)
    (zero : P) (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (select : Bool → Bool) :
    (adaptedProcess F c).lower.executeDensity UA Ub select
      (basis ((adaptedRegister chart).index (adaptedZero (chart := chart) zero)))=
      (c.lower F).executeDensity (dilationEncoding UA) (preparation Ub) select
        (basis ((Fintype.equivFin P) zero)) := by
  have h:=c.adapt_executeDensity F UA Ub select (Pi.single zero 1)
  rw [initialState_single (chart := chart) zero,
    finiteVector_single (Physical.coordinates (enableCoordinates chart)) (adaptedZero (chart := chart) zero),
    finiteVector_single chart zero] at h
  rw [adaptedProcess_lower]
  exact h

theorem adaptedProcess_returns (F : OutputLayout chart n) (c : AnyProgram chart a n)
    (Pred : (Fin (doubledRegister n).dimension → ℂ) → Prop) (hzero : Pred 0)
    (zero : P) (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    Returns Pred UA Ub (adaptedProcess F c).lower
      (basis ((adaptedRegister chart).index (adaptedZero (chart := chart) zero))) ↔
      Returns Pred (dilationEncoding UA) (preparation Ub) (c.lower F)
        (basis ((Fintype.equivFin P) zero)) := by
  have h:=c.adapt_returns F Pred hzero UA Ub (Pi.single zero 1)
  rw [initialState_single (chart := chart) zero,
    finiteVector_single (Physical.coordinates (enableCoordinates chart)) (adaptedZero (chart := chart) zero),
    finiteVector_single chart zero] at h
  rw [adaptedProcess_lower]
  exact h

def reducedProcess (F : OutputLayout chart n) (c : AnyProgram chart a n) :
    Process (matrixArguments a n) (Equiv.refl (Bits n)) (dataRegister n)
      (poolRegister (adaptedRegister chart) n 3) :=
  freshProcess n (adaptedRegister chart) (adaptedProcess F c) 3

def reducedInput (zero : P) : Fin (poolRegister (adaptedRegister chart) n 3).dimension → ℂ :=
  poolBasis (adaptedRegister chart) n (adaptedZero zero) (fun _=>false) 3

theorem reducedProcess_resources (F : OutputLayout chart n) (c : AnyProgram chart a n) :
    (reducedProcess F c).work≤3*c.work+14406*c.matrixCalls+3*c.vectorCalls ∧
    (reducedProcess F c).measurements≤3*(c.measurements+1) ∧
    matrixDepth (reducedProcess F c).lower≤6*c.matrixCalls ∧
    (reducedProcess F c).lower.vectorDepth≤3*c.vectorCalls ∧
    RegisterBound (2^(4*Fintype.card W+16)) (reducedProcess F c).lower := by
  have ha:=adaptedProcess_resources F c
  have hb:=freshProcess_resources n (adaptedRegister chart) (adaptedProcess F c) 3
  have hq:=freshProcess_query_depths n (adaptedRegister chart) (adaptedProcess F c) 3
  have hs:=fresh_three_registerBound n (adaptedRegister chart) (adaptedProcess F c)
  rw [ha.2.2.2] at hb
  rw [ha.2.1,ha.2.2.1] at hq
  rw [adaptedRegister_qubits] at hs
  have he:4*(Fintype.card W+4)=4*Fintype.card W+16 := by omega
  rw [he] at hs
  refine ⟨?_,hb.2.1,?_,hq.2,hs⟩
  · change (freshProcess n (adaptedRegister chart) (adaptedProcess F c) 3).work≤_
    nlinarith only [hb.1,ha.1]
  · change matrixDepth (freshProcess n (adaptedRegister chart) (adaptedProcess F c) 3).lower≤_
    simpa only [←Nat.mul_assoc] using hq.1

end OptimalQLS.Reduction.GenericSolver.FreshCopies
