import OptimalQLS.Reduction.GenericSolver.PhysicalAdaptSafety

/-! Branchwise refinement of the actual physical lowering, including the
extra zero-mass branches from tracing the clean scratch register. -/
noncomputable section
open scoped Classical BigOperators
namespace OptimalQLS.Reduction.GenericSolver.FreshCopies
open Matrix LowerBounds PolynomialTransform TransducerCompiler BinaryClock
open Refinement.CostedExecution Physical
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
variable {P W D V : Type} [Fintype P] [DecidableEq P] [Fintype D] [DecidableEq D]
  {chart : P ≃ (W → Bool)} {dataChart : D ≃ (V → Bool)} {a n : ℕ}
namespace SourceProgram

theorem adapt_runReturns (F : TensorLayout chart dataChart) (c : SourceProgram chart a n)
    (Pred : (Fin (Fintype.card D) → ℂ) → Prop) (hzero : Pred 0)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (v : P → ℂ) :
    (c.adapt F).runReturns Pred gateEval UA Ub (inserted (Equiv.refl _) (false,false,false) v) ↔
      (c.toPhysical F).runReturns Pred TransducerCompiler.Physical.LocalGate.eval
        (dilationEncoding UA) (preparation Ub) v := by
  induction c generalizing v with
  | step i next ih =>
    simp only [adapt,toPhysical,PhysicalProgram.runReturns_prepend]
    have hi := inserted_intertwines (Equiv.refl (P × PhaseScratch)) (false,false,false)
      _ _ (instructionCode_intertwines i UA Ub) v
    rw [hi,ih]
    simp [NamedCircuit.toQuery,NamedInstruction.toQuery,QueryCircuit.eval]
  | measure i next ih =>
    simp only [adapt,toPhysical,PhysicalProgram.runReturns]
    apply forall_congr'
    intro b
    have hm := measuredBit_inserted (Equiv.refl (P × PhaseScratch))
      (oldEmbedding (chart := chart)) (false,false,false) i (outcome b) v
    change measuredBit (Physical.coordinates chart) (.inl i) (outcome b)*ᵥ
      inserted (Equiv.refl _) (false,false,false) v = _ at hm
    rw [hm]
    exact ih _ _
  | finish flag =>
    exact extendedLayout_returns (Equiv.refl (P × PhaseScratch)) oldEmbedding F
      (false,false,false) v flag Pred hzero

theorem adapt_returns (F : TensorLayout chart dataChart) (c : SourceProgram chart a n)
    (Pred : (Fin (Fintype.card D) → ℂ) → Prop) (hzero : Pred 0)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (v : P → ℂ) :
    Returns Pred UA Ub ((c.adapt F).lower gateEval)
      (finiteVector (inserted (Equiv.refl _) (false,false,false) v)) ↔
    Returns Pred (dilationEncoding UA) (preparation Ub) (c.lower F) (finiteVector v) := by
  rw [PhysicalProgram.lower_runReturns,adapt_runReturns F c Pred hzero]
  exact (PhysicalProgram.lower_runReturns Pred _ _ _ (c.toPhysical F) v).symm

end SourceProgram
end OptimalQLS.Reduction.GenericSolver.FreshCopies
