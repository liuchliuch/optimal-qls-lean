import OptimalQLS.Reduction.GenericSolver.FreshCopiesProcess
import OptimalQLS.Reduction.GenericSolver.Branchwise

/-! Actual-register vector semantics of the same physical process. -/
noncomputable section
open scoped Classical BigOperators
namespace OptimalQLS.Reduction.GenericSolver.FreshCopies
open Matrix LowerBounds PolynomialTransform TransducerCompiler
open Refinement.CostedExecution Refinement.Repetition
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

def indexedVector (R : Register) (v : R.State → ℂ) : Fin R.dimension → ℂ :=
  v ∘ R.index.symm

theorem indexedMatrix_mulVec (R Q : Register) (M : Matrix Q.State R.State ℂ)
    (v : R.State → ℂ) :
    indexedMatrix R Q M*ᵥindexedVector R v=indexedVector Q (M*ᵥv) := by
  simpa [indexedMatrix,indexedVector,Function.comp_def] using
    Matrix.submatrix_mulVec_equiv M (indexedVector R v) Q.index.symm R.index.symm

theorem indexedVector_smul (R : Register) (v : R.State → ℂ) (c : ℂ) :
    indexedVector R (c • v)=c • indexedVector R v := rfl

theorem indexedVector_product (R T : Register) (v : R.State → ℂ) (z : T.State → ℂ) :
    indexedVector (R.product T) (fun p=>v p.1*z p.2)=
      tensorVector (indexedVector R v) (indexedVector T z) := by
  ext i
  simp [indexedVector,tensorVector,Register.product]

theorem indexedVector_comp_index (R : Register) (v : Fin R.dimension → ℂ) :
    indexedVector R (v ∘ R.index)=v := by
  ext i
  simp [indexedVector]

variable {A B VA VB : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable {argumentsA : A ≃ (VA → Bool)} {argumentsB : B ≃ (VB → Bool)} {O R : Register}
namespace Process

def runDensity (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (select : Bool → Bool) : {R : Register} → Process argumentsA argumentsB O R →
      (R.State → ℂ) → Matrix (Fin O.dimension) (Fin O.dimension) ℂ
  | _,.unitary U _ next,v => next.runDensity UA Ub select (U.val*ᵥv)
  | _,.matrix p adj _ next,v => next.runDensity UA Ub select
      ((p.apply (if adj then UA⁻¹ else UA)).val*ᵥv)
  | _,.vector p adj _ next,v => next.runDensity UA Ub select
      ((p.apply (if adj then Ub⁻¹ else Ub)).val*ᵥv)
  | R,.measure i next,v => ∑ b : Fin 2,(next (outcome b)).runDensity UA Ub select
      (measuredBit R.bits i (outcome b)*ᵥv)
  | _,.trace F next,v => ∑ r : F.Rest,next.runDensity UA Ub select (F.kraus r*ᵥv)
  | _,.output flag,v => if select flag then pureDensity (indexedVector O v) else 0

theorem lower_runDensity (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (select : Bool → Bool) (p : Process argumentsA argumentsB O R) (v : R.State → ℂ) :
    p.lower.executeDensity UA Ub select (indexedVector R v)=p.runDensity UA Ub select v := by
  induction p with
  | unitary U h next ih =>
    simp only [lower,FiniteOracleProgram.executeDensity,Fin.sum_univ_one]
    change next.lower.executeDensity UA Ub select (indexedMatrix _ _ U.val*ᵥindexedVector _ v)=_
    rw [indexedMatrix_mulVec,ih]
    rfl
  | matrix p adj L next ih =>
    simp only [lower,FiniteOracleProgram.executeDensity,reindexPort_apply]
    change next.lower.executeDensity UA Ub select
      (indexedMatrix _ _ (p.apply (if adj then UA⁻¹ else UA)).val*ᵥindexedVector _ v)=_
    rw [indexedMatrix_mulVec,ih]
    rfl
  | vector p adj L next ih =>
    simp only [lower,FiniteOracleProgram.executeDensity,reindexPort_apply]
    change next.lower.executeDensity UA Ub select
      (indexedMatrix _ _ (p.apply (if adj then Ub⁻¹ else Ub)).val*ᵥindexedVector _ v)=_
    rw [indexedMatrix_mulVec,ih]
    rfl
  | measure i next ih =>
    simp only [lower,FiniteOracleProgram.executeDensity,indexedMatrix_mulVec,ih,runDensity]
  | trace F next ih =>
    simp only [lower,FiniteOracleProgram.executeDensity,TensorLayout.indexedKraus,
      indexedMatrix_mulVec,ih,runDensity]
    exact (Fintype.equivFin F.Rest).symm.sum_comp (fun r=>next.runDensity UA Ub select (F.kraus r*ᵥv))
  | output flag => rfl

def runReturns (Pred : (Fin O.dimension → ℂ) → Prop)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    {R : Register} → Process argumentsA argumentsB O R → (R.State → ℂ) → Prop
  | _,.unitary U _ next,v => next.runReturns Pred UA Ub (U.val*ᵥv)
  | _,.matrix p adj _ next,v => next.runReturns Pred UA Ub
      ((p.apply (if adj then UA⁻¹ else UA)).val*ᵥv)
  | _,.vector p adj _ next,v => next.runReturns Pred UA Ub
      ((p.apply (if adj then Ub⁻¹ else Ub)).val*ᵥv)
  | R,.measure i next,v => ∀ b : Fin 2,(next (outcome b)).runReturns Pred UA Ub
      (measuredBit R.bits i (outcome b)*ᵥv)
  | _,.trace F next,v => ∀ r : F.Rest,next.runReturns Pred UA Ub (F.kraus r*ᵥv)
  | _,.output flag,v => flag=true → Pred (indexedVector O v)

theorem lower_runReturns (Pred : (Fin O.dimension → ℂ) → Prop)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (p : Process argumentsA argumentsB O R) (v : R.State → ℂ) :
    Returns Pred UA Ub p.lower (indexedVector R v) ↔ p.runReturns Pred UA Ub v := by
  induction p with
  | unitary U h next ih =>
    change (∀ i : Fin 1,Returns Pred UA Ub next.lower
      (indexedMatrix _ _ U.val*ᵥindexedVector _ v)) ↔ _
    simp only [Fin.forall_fin_one,indexedMatrix_mulVec,ih,runReturns]
  | matrix p adj L next ih =>
    simp only [lower,Returns,reindexPort_apply]
    change Returns Pred UA Ub next.lower
      (indexedMatrix _ _ (p.apply (if adj then UA⁻¹ else UA)).val*ᵥindexedVector _ v) ↔ _
    rw [indexedMatrix_mulVec,ih]
    rfl
  | vector p adj L next ih =>
    simp only [lower,Returns,reindexPort_apply]
    change Returns Pred UA Ub next.lower
      (indexedMatrix _ _ (p.apply (if adj then Ub⁻¹ else Ub)).val*ᵥindexedVector _ v) ↔ _
    rw [indexedMatrix_mulVec,ih]
    rfl
  | measure i next ih =>
    simp only [lower,Returns,indexedMatrix_mulVec,ih,runReturns]
  | trace F next ih =>
    simp only [lower,Returns,TensorLayout.indexedKraus,indexedMatrix_mulVec,ih,runReturns]
    constructor
    · intro h r
      simpa only [Equiv.symm_apply_apply] using h ((Fintype.equivFin F.Rest) r)
    · intro h r
      exact h _
  | output flag => rfl

theorem runReturns_smul (Pred : (Fin O.dimension → ℂ) → Prop)
    (hPred : ∀ v (c : ℂ),Pred v→Pred (c • v))
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (p : Process argumentsA argumentsB O R) (v : R.State → ℂ)
    (h : p.runReturns Pred UA Ub v) (c : ℂ) : p.runReturns Pred UA Ub (c • v) := by
  rw [←lower_runReturns,indexedVector_smul]
  exact returns_smul Pred hPred p.lower UA Ub _ ((lower_runReturns Pred UA Ub p v).mpr h) c

theorem runDensity_smul (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (select : Bool → Bool) (p : Process argumentsA argumentsB O R) (v : R.State → ℂ) (c : ℂ) :
    p.runDensity UA Ub select (c • v)=Complex.normSq c • p.runDensity UA Ub select v := by
  rw [←lower_runDensity,indexedVector_smul,executeDensity_smul,lower_runDensity]

end Process
end OptimalQLS.Reduction.GenericSolver.FreshCopies
