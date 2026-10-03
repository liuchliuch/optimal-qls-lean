import OptimalQLS.Reduction.GenericSolver.PhysicalExtension
import OptimalQLS.Reduction.GenericSolver.PhysicalComplete

/-! The full arbitrary branching solver is adapted to the original supplied
oracles. All new unitary cost comes from the actual instructionCode words. -/
noncomputable section
open scoped Classical BigOperators
namespace OptimalQLS.Reduction.GenericSolver.FreshCopies
open Matrix LowerBounds PolynomialTransform TransducerCompiler BinaryClock
open Refinement.CostedExecution Physical
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
variable {P W D V : Type} [Fintype P] [DecidableEq P] [Fintype D] [DecidableEq D]
  {chart : P ≃ (W → Bool)} {dataChart : D ≃ (V → Bool)} {a n : ℕ}

namespace PhysicalProgram
variable {G : Type*} {A B : Type}

theorem prepend_measurements (c : NamedCircuit G A B P) (next : PhysicalProgram G A B chart dataChart) :
    (prepend c next).measurements=next.measurements := by
  induction c with
  | nil => rfl
  | cons i c ih => cases i <;> exact ih

end PhysicalProgram

namespace SourceProgram

def adapt (F : TensorLayout chart dataChart) : SourceProgram chart a n →
    PhysicalProgram (Physical.Gate chart a n) (Bits a × Bits n) (Bits n)
      (Physical.coordinates chart) dataChart
  | .step i next => PhysicalProgram.prepend (instructionCode i) (next.adapt F)
  | .measure i next => .measure (.inl i) (fun b=>(next b).adapt F)
  | .finish flag => .finish (extendedLayout (Equiv.refl (P × PhaseScratch)) oldEmbedding F) flag

theorem adapt_work (F : TensorLayout chart dataChart) (c : SourceProgram chart a n) :
    (c.adapt F).work≤c.work+4801*c.matrixCalls := by
  induction c with
  | step i next ih =>
    rw [adapt,PhysicalProgram.prepend_work]
    have hi := (instructionCode_counts i).2.2
    simp only [work,matrixCalls]
    omega
  | measure i next ih =>
    simp only [adapt,PhysicalProgram.work,work,matrixCalls]
    have hf := ih false
    have ht := ih true
    omega
  | finish flag => simp [adapt,PhysicalProgram.work,work,matrixCalls]

theorem adapt_matrixCalls (F : TensorLayout chart dataChart) (c : SourceProgram chart a n) :
    (c.adapt F).matrixCalls=2*c.matrixCalls := by
  induction c with
  | step i next ih =>
    rw [adapt,PhysicalProgram.prepend_matrixCalls gateEval,(instructionCode_counts i).1,ih]
    simp [matrixCalls,Nat.mul_add]
  | measure i next ih =>
    simp only [adapt,PhysicalProgram.matrixCalls,matrixCalls,ih]
    exact (mul_max 2 (next false).matrixCalls (next true).matrixCalls).symm
  | finish flag => rfl

theorem adapt_vectorCalls (F : TensorLayout chart dataChart) (c : SourceProgram chart a n) :
    (c.adapt F).vectorCalls=c.vectorCalls := by
  induction c with
  | step i next ih =>
    rw [adapt,PhysicalProgram.prepend_vectorCalls gateEval,(instructionCode_counts i).2.1,ih]
    rfl
  | measure i next ih => simp [adapt,PhysicalProgram.vectorCalls,vectorCalls,ih]
  | finish flag => rfl

theorem adapt_measurements (F : TensorLayout chart dataChart) (c : SourceProgram chart a n) :
    (c.adapt F).measurements=c.measurements := by
  induction c with
  | step i next ih => rw [adapt,PhysicalProgram.prepend_measurements,ih]; rfl
  | measure i next ih => simp [adapt,PhysicalProgram.measurements,measurements,ih]
  | finish flag => rfl

theorem adapt_runDensity (F : TensorLayout chart dataChart) (c : SourceProgram chart a n)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (select : Bool → Bool) (v : P → ℂ) :
    (c.adapt F).runDensity gateEval UA Ub select (inserted (Equiv.refl _) (false,false,false) v)=
      (c.toPhysical F).runDensity TransducerCompiler.Physical.LocalGate.eval
        (dilationEncoding UA) (preparation Ub) select v := by
  induction c generalizing v with
  | step i next ih =>
    simp only [adapt,toPhysical,PhysicalProgram.runDensity_prepend]
    have hi := inserted_intertwines (Equiv.refl (P × PhaseScratch)) (false,false,false)
      _ _ (instructionCode_intertwines i UA Ub) v
    rw [hi,ih]
    simp [NamedCircuit.toQuery,NamedInstruction.toQuery,QueryCircuit.eval]
  | measure i next ih =>
    simp only [adapt,toPhysical,PhysicalProgram.runDensity]
    apply Finset.sum_congr rfl
    intro b _
    have hm := measuredBit_inserted (Equiv.refl (P × PhaseScratch))
      (oldEmbedding (chart := chart)) (false,false,false) i (outcome b) v
    change measuredBit (Physical.coordinates chart) (.inl i) (outcome b)*ᵥ
      inserted (Equiv.refl _) (false,false,false) v = _ at hm
    rw [hm]
    exact ih _ _
  | finish flag =>
    exact extendedLayout_density (Equiv.refl (P × PhaseScratch)) oldEmbedding F
      (false,false,false) v (select flag)

/-- Equality of the actual lowered finite-program densities, including
failure outputs and arbitrary mixed-state decompositions by linearity. -/
theorem adapt_executeDensity (F : TensorLayout chart dataChart) (c : SourceProgram chart a n)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (select : Bool → Bool) (v : P → ℂ) :
    ((c.adapt F).lower gateEval).executeDensity UA Ub select
      (finiteVector (inserted (Equiv.refl _) (false,false,false) v))=
    (c.lower F).executeDensity (dilationEncoding UA) (preparation Ub) select (finiteVector v) := by
  rw [PhysicalProgram.lower_runDensity,adapt_runDensity]
  exact (PhysicalProgram.lower_runDensity _ _ _ _ (c.toPhysical F) v).symm

end SourceProgram
end OptimalQLS.Reduction.GenericSolver.FreshCopies
