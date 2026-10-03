import OptimalQLS.Reduction.GenericSolver.FreshCopiesSourceLower
import OptimalQLS.Reduction.GenericSolver.Branchwise

/-! Convenient coordinate-free vector semantics, proved equal to the actual
finite-register lowering. Output indices use the existing fixed enumeration. -/
noncomputable section
open scoped Classical BigOperators
namespace OptimalQLS.Reduction.GenericSolver.FreshCopies
open Matrix LowerBounds PolynomialTransform TransducerCompiler
open Refinement.CostedExecution
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
variable {P W D V : Type} [Fintype P] [DecidableEq P] [Fintype D] [DecidableEq D]
  {chart : P ≃ (W → Bool)} {dataChart : D ≃ (V → Bool)}

def finiteVector (v : P → ℂ) : Fin (Fintype.card P) → ℂ := v ∘ (Fintype.equivFin P).symm

theorem finiteMatrix_mulVec (M : Matrix D P ℂ) (v : P → ℂ) :
    finiteMatrix M*ᵥfiniteVector v=finiteVector (M*ᵥv) := by
  simpa [finiteMatrix,finiteVector,Function.comp_def] using
    Matrix.submatrix_mulVec_equiv M (finiteVector v) (Fintype.equivFin D).symm (Fintype.equivFin P).symm

namespace PhysicalProgram
variable {G : Type*} {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def runDensity (gate : G → Matrix.unitaryGroup P ℂ)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (select : Bool → Bool) :
    PhysicalProgram G A B chart dataChart → (P → ℂ) → Matrix (Fin (Fintype.card D)) (Fin (Fintype.card D)) ℂ
  | .named g next, v => next.runDensity gate UA Ub select ((gate g).val*ᵥv)
  | .matrix p adj next, v => next.runDensity gate UA Ub select ((p.apply (if adj then UA⁻¹ else UA)).val*ᵥv)
  | .vector p adj next, v => next.runDensity gate UA Ub select ((p.apply (if adj then Ub⁻¹ else Ub)).val*ᵥv)
  | .measure i next, v => ∑ b : Fin 2,(next (outcome b)).runDensity gate UA Ub select
      (measuredBit chart i (outcome b)*ᵥv)
  | .finish F flag, v => ∑ r : F.Rest, if select flag then pureDensity (finiteVector (F.kraus r*ᵥv)) else 0

theorem lower_runDensity (gate : G → Matrix.unitaryGroup P ℂ)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (select : Bool → Bool)
    (tree : PhysicalProgram G A B chart dataChart) (v : P → ℂ) :
    (tree.lower gate).executeDensity UA Ub select (finiteVector v)=tree.runDensity gate UA Ub select v := by
  induction tree generalizing v with
  | named g next ih =>
    simp only [lower,FiniteOracleProgram.executeDensity,Fin.sum_univ_one]
    change (next.lower gate).executeDensity UA Ub select (finiteMatrix (gate g).val*ᵥfiniteVector v)=_
    rw [finiteMatrix_mulVec,ih]
    rfl
  | matrix p adj next ih =>
    simp only [lower,FiniteOracleProgram.executeDensity,Refinement.Repetition.reindexPort_apply]
    change (next.lower gate).executeDensity UA Ub select
      (finiteMatrix (p.apply (if adj then UA⁻¹ else UA)).val*ᵥfiniteVector v)=_
    rw [finiteMatrix_mulVec,ih]
    rfl
  | vector p adj next ih =>
    simp only [lower,FiniteOracleProgram.executeDensity,Refinement.Repetition.reindexPort_apply]
    change (next.lower gate).executeDensity UA Ub select
      (finiteMatrix (p.apply (if adj then Ub⁻¹ else Ub)).val*ᵥfiniteVector v)=_
    rw [finiteMatrix_mulVec,ih]
    rfl
  | measure i next ih =>
    simp only [lower,FiniteOracleProgram.executeDensity,finiteMatrix_mulVec,ih,runDensity]
  | finish F flag =>
    simp only [lower,FiniteOracleProgram.executeDensity,finiteMatrix_mulVec,runDensity]
    exact (Fintype.equivFin F.Rest).symm.sum_comp
      (fun r=>if select flag then pureDensity (finiteVector (F.kraus r*ᵥv)) else 0)

theorem runDensity_prepend (gate : G → Matrix.unitaryGroup P ℂ)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (select : Bool → Bool)
    (c : NamedCircuit G A B P) (next : PhysicalProgram G A B chart dataChart) (v : P → ℂ) :
    (prepend c next).runDensity gate UA Ub select v=
      next.runDensity gate UA Ub select (((c.toQuery gate).eval UA Ub).val*ᵥv) := by
  induction c generalizing v with
  | nil => simp [prepend,NamedCircuit.toQuery,QueryCircuit.eval]
  | cons i c ih => cases i <;>
      simp [prepend,runDensity,NamedCircuit.toQuery,NamedInstruction.toQuery,
        QueryCircuit.eval,QueryInstruction.eval,ih,←Matrix.mulVec_mulVec]

/-- Every actual success branch, retaining the Kraus outcome index. -/
def runReturns (Pred : (Fin (Fintype.card D) → ℂ) → Prop)
    (gate : G → Matrix.unitaryGroup P ℂ)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    PhysicalProgram G A B chart dataChart → (P → ℂ) → Prop
  | .named g next, v => next.runReturns Pred gate UA Ub ((gate g).val*ᵥv)
  | .matrix p adj next, v => next.runReturns Pred gate UA Ub ((p.apply (if adj then UA⁻¹ else UA)).val*ᵥv)
  | .vector p adj next, v => next.runReturns Pred gate UA Ub ((p.apply (if adj then Ub⁻¹ else Ub)).val*ᵥv)
  | .measure i next, v => ∀ b : Fin 2,(next (outcome b)).runReturns Pred gate UA Ub
      (measuredBit chart i (outcome b)*ᵥv)
  | .finish F flag, v => ∀ r : F.Rest, flag=true → Pred (finiteVector (F.kraus r*ᵥv))

theorem lower_runReturns (Pred : (Fin (Fintype.card D) → ℂ) → Prop)
    (gate : G → Matrix.unitaryGroup P ℂ)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (tree : PhysicalProgram G A B chart dataChart) (v : P → ℂ) :
    Returns Pred UA Ub (tree.lower gate) (finiteVector v) ↔ tree.runReturns Pred gate UA Ub v := by
  induction tree generalizing v with
  | named g next ih =>
    change (∀ i : Fin 1,Returns Pred UA Ub (next.lower gate)
      (finiteMatrix (gate g).val*ᵥfiniteVector v)) ↔ _
    simp only [Fin.forall_fin_one,finiteMatrix_mulVec,ih,runReturns]
  | matrix p adj next ih =>
    simp only [lower,Returns,Refinement.Repetition.reindexPort_apply]
    change Returns Pred UA Ub (next.lower gate)
      (finiteMatrix (p.apply (if adj then UA⁻¹ else UA)).val*ᵥfiniteVector v) ↔ _
    rw [finiteMatrix_mulVec,ih]
    rfl
  | vector p adj next ih =>
    simp only [lower,Returns,Refinement.Repetition.reindexPort_apply]
    change Returns Pred UA Ub (next.lower gate)
      (finiteMatrix (p.apply (if adj then Ub⁻¹ else Ub)).val*ᵥfiniteVector v) ↔ _
    rw [finiteMatrix_mulVec,ih]
    rfl
  | measure i next ih =>
    simp only [lower,Returns,finiteMatrix_mulVec,ih,runReturns]
  | finish F flag =>
    simp only [lower,Returns,finiteMatrix_mulVec,runReturns]
    constructor
    · intro h r
      simpa only [Equiv.symm_apply_apply] using h ((Fintype.equivFin F.Rest) r)
    · intro h r
      exact h _

theorem runReturns_prepend (Pred : (Fin (Fintype.card D) → ℂ) → Prop)
    (gate : G → Matrix.unitaryGroup P ℂ)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (c : NamedCircuit G A B P) (next : PhysicalProgram G A B chart dataChart) (v : P → ℂ) :
    (prepend c next).runReturns Pred gate UA Ub v=
      next.runReturns Pred gate UA Ub (((c.toQuery gate).eval UA Ub).val*ᵥv) := by
  induction c generalizing v with
  | nil => simp [prepend,NamedCircuit.toQuery,QueryCircuit.eval]
  | cons i c ih => cases i <;>
      simp [prepend,runReturns,NamedCircuit.toQuery,NamedInstruction.toQuery,
        QueryCircuit.eval,QueryInstruction.eval,ih,←Matrix.mulVec_mulVec]

end PhysicalProgram
end OptimalQLS.Reduction.GenericSolver.FreshCopies
