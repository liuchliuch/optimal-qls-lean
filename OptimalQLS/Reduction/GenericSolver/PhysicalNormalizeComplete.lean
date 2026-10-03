import OptimalQLS.Reduction.GenericSolver.PhysicalNormalizeSemantics
import OptimalQLS.Reduction.GenericSolver.PhysicalAdaptBranches

/-! Generic physical normalization/reduction before fresh-copy repetition,
including optional ordinary calls. All costs belong to the emitted same tree. -/
noncomputable section
open scoped Classical BigOperators
namespace OptimalQLS.Reduction.GenericSolver.Physical
open Matrix LowerBounds PolynomialTransform TransducerCompiler BinaryClock
open Refinement.CostedExecution FreshCopies
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
variable {P W D V : Type} [Fintype P] [DecidableEq P] [Fintype D] [DecidableEq D]
  {chart : P ≃ (W → Bool)} {dataChart : D ≃ (V → Bool)} {a n : ℕ}

theorem AnyInstruction.source_counts (i : AnyInstruction chart a n) :
    NamedCircuit.workGates [i.sourceQuery]=i.work ∧
    (NamedCircuit.toQuery TransducerCompiler.Physical.LocalGate.eval [i.sourceQuery]).matrixQueries=i.matrixCalls ∧
    (NamedCircuit.toQuery TransducerCompiler.Physical.LocalGate.eval [i.sourceQuery]).vectorQueries=i.vectorCalls := by
  cases i with
  | core i => cases i <;> exact ⟨rfl,rfl,rfl⟩
  | matrix F adj => exact ⟨rfl,rfl,rfl⟩
  | vector F adj => exact ⟨rfl,rfl,rfl⟩

namespace AnyProgram

theorem toPhysical_work (F : TensorLayout chart dataChart) (c : AnyProgram chart a n) :
    (c.toPhysical F).work=c.work := by
  induction c with
  | step i next ih => rw [toPhysical,PhysicalProgram.prepend_work,(i.source_counts).1,ih]; rfl
  | measure i next ih => simp [toPhysical,PhysicalProgram.work,work,ih]
  | finish flag => rfl

theorem toPhysical_matrixCalls (F : TensorLayout chart dataChart) (c : AnyProgram chart a n) :
    (c.toPhysical F).matrixCalls=c.matrixCalls := by
  induction c with
  | step i next ih =>
    rw [toPhysical,PhysicalProgram.prepend_matrixCalls TransducerCompiler.Physical.LocalGate.eval,
      (i.source_counts).2.1,ih]
    rfl
  | measure i next ih => simp [toPhysical,PhysicalProgram.matrixCalls,matrixCalls,ih]
  | finish flag => rfl

theorem toPhysical_vectorCalls (F : TensorLayout chart dataChart) (c : AnyProgram chart a n) :
    (c.toPhysical F).vectorCalls=c.vectorCalls := by
  induction c with
  | step i next ih =>
    rw [toPhysical,PhysicalProgram.prepend_vectorCalls TransducerCompiler.Physical.LocalGate.eval,
      (i.source_counts).2.2,ih]
    rfl
  | measure i next ih => simp [toPhysical,PhysicalProgram.vectorCalls,vectorCalls,ih]
  | finish flag => rfl

theorem toPhysical_measurements (F : TensorLayout chart dataChart) (c : AnyProgram chart a n) :
    (c.toPhysical F).measurements=c.measurements := by
  induction c with
  | step i next ih => rw [toPhysical,PhysicalProgram.prepend_measurements,ih]; rfl
  | measure i next ih => simp [toPhysical,PhysicalProgram.measurements,measurements,ih]
  | finish flag => rfl

def adapt (F : TensorLayout chart dataChart) (c : AnyProgram chart a n) :=
  c.normalize.adapt (enableLayout F)

def initialState (v : P → ℂ) : ((Bool × P) × PhaseScratch) → ℂ :=
  inserted (Equiv.refl _) (false,false,false) (inserted (Equiv.prodComm P Bool) false v)

theorem adapt_resources (F : TensorLayout chart dataChart) (c : AnyProgram chart a n) :
    (c.adapt F).work≤c.work+4802*c.matrixCalls+c.vectorCalls ∧
    (c.adapt F).matrixCalls=2*c.matrixCalls ∧
    (c.adapt F).vectorCalls=c.vectorCalls ∧
    (c.adapt F).measurements=c.measurements := by
  have hc := c.normalize_counts
  have hi := c.initializationCost_le_queries
  have hw := c.normalize.adapt_work (enableLayout F)
  have hA := c.normalize.adapt_matrixCalls (enableLayout F)
  have hB := c.normalize.adapt_vectorCalls (enableLayout F)
  have hm := c.normalize.adapt_measurements (enableLayout F)
  change _≤_ ∧ _=_ ∧ _=_ ∧ _=_
  simp only [adapt]
  omega

theorem adapt_safe (F : TensorLayout chart dataChart) (c : AnyProgram chart a n) :
    (c.adapt F).Safe gateEval (matrixArguments a n) (Equiv.refl (Bits n)) :=
  c.normalize.adapt_safe (enableLayout F)

theorem adapt_executeDensity (F : TensorLayout chart dataChart) (c : AnyProgram chart a n)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (select : Bool → Bool) (v : P → ℂ) :
    ((c.adapt F).lower gateEval).executeDensity UA Ub select (finiteVector (initialState v))=
      (c.lower F).executeDensity (dilationEncoding UA) (preparation Ub) select (finiteVector v) := by
  rw [adapt,initialState,SourceProgram.adapt_executeDensity]
  exact c.normalize_executeDensity F _ _ select v

theorem adapt_returns (F : TensorLayout chart dataChart) (c : AnyProgram chart a n)
    (Pred : (Fin (Fintype.card D) → ℂ) → Prop) (hzero : Pred 0)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (v : P → ℂ) :
    Returns Pred UA Ub ((c.adapt F).lower gateEval) (finiteVector (initialState v)) ↔
    Returns Pred (dilationEncoding UA) (preparation Ub) (c.lower F) (finiteVector v) := by
  rw [adapt,initialState,SourceProgram.adapt_returns _ _ Pred hzero]
  exact c.normalize_returns F Pred hzero _ _ v

theorem register_card [Fintype W] (chart : P ≃ (W → Bool)) :
    Fintype.card ((Bool × P) × PhaseScratch)=2^(Fintype.card W+4) := by
  rw [Physical.space_card (enableCoordinates chart)]
  simp only [Fintype.card_sum,Fintype.card_unit]
  congr 1
  omega

end AnyProgram
end OptimalQLS.Reduction.GenericSolver.Physical
