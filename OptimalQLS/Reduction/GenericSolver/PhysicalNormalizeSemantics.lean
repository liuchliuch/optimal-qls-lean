import OptimalQLS.Reduction.GenericSolver.PhysicalNormalizeProgram
import OptimalQLS.Reduction.GenericSolver.PhysicalExtension

/-! Actual branching execution equivalence for optional-control normalization.
The enable bit is initialized by an emitted X, then remains a spectator of all
old work and measurements. Its final partial trace adds only zero-mass branches. -/
noncomputable section
open scoped Classical BigOperators
namespace OptimalQLS.Reduction.GenericSolver.Physical
open Matrix LowerBounds PolynomialTransform TransducerCompiler BinaryClock
open Refinement.CostedExecution FreshCopies
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
variable {P W D V : Type} [Fintype P] [DecidableEq P] [Fintype D] [DecidableEq D]
  {chart : P ≃ (W → Bool)} {dataChart : D ≃ (V → Bool)} {a n : ℕ}

namespace AnyProgram

theorem body_runDensity (F : TensorLayout chart dataChart) (c : AnyProgram chart a n)
    (UA : Matrix.unitaryGroup (Bits a × (Bits n ⊕ Bits n)) ℂ)
    (Ub : Matrix.unitaryGroup (Bits n ⊕ Bits n) ℂ) (select : Bool → Bool)
    (b : Bool) (hb : c.hasPlain=true → b=true) (v : P → ℂ) :
    (c.body.toPhysical (enableLayout F)).runDensity TransducerCompiler.Physical.LocalGate.eval UA Ub select
      (inserted (Equiv.prodComm P Bool) b v)=
    (c.toPhysical F).runDensity TransducerCompiler.Physical.LocalGate.eval UA Ub select v := by
  induction c generalizing b v with
  | step i next ih =>
    simp only [body,SourceProgram.toPhysical,toPhysical,PhysicalProgram.runDensity_prepend,
      NamedCircuit.toQuery,List.map_cons,List.map_nil,QueryCircuit.eval,one_mul]
    have hi := inserted_intertwines (Equiv.prodComm P Bool) b _ _
      (i.normalize_intertwines UA Ub b (fun h=>hb (by simp [hasPlain,h]))) v
    rw [hi]
    exact ih b (fun h=>hb (by simp [hasPlain,h])) _
  | measure i next ih =>
    simp only [body,SourceProgram.toPhysical,toPhysical,PhysicalProgram.runDensity]
    apply Finset.sum_congr rfl
    intro t _
    have hm := measuredBit_inserted (Equiv.prodComm P Bool)
      (sourceEnableEmbedding (chart := chart)) b i (outcome t) v
    change measuredBit (enableCoordinates chart) (.inr i) (outcome t)*ᵥ
      inserted (Equiv.prodComm P Bool) b v = _ at hm
    rw [hm]
    apply ih
    intro h
    apply hb
    cases ht : outcome t <;> simp_all [hasPlain]
  | finish flag =>
    exact extendedLayout_density (Equiv.prodComm P Bool) sourceEnableEmbedding F b v (select flag)

theorem body_runReturns (F : TensorLayout chart dataChart) (c : AnyProgram chart a n)
    (Pred : (Fin (Fintype.card D) → ℂ) → Prop) (hzero : Pred 0)
    (UA : Matrix.unitaryGroup (Bits a × (Bits n ⊕ Bits n)) ℂ)
    (Ub : Matrix.unitaryGroup (Bits n ⊕ Bits n) ℂ)
    (b : Bool) (hb : c.hasPlain=true → b=true) (v : P → ℂ) :
    (c.body.toPhysical (enableLayout F)).runReturns Pred TransducerCompiler.Physical.LocalGate.eval UA Ub
      (inserted (Equiv.prodComm P Bool) b v) ↔
    (c.toPhysical F).runReturns Pred TransducerCompiler.Physical.LocalGate.eval UA Ub v := by
  induction c generalizing b v with
  | step i next ih =>
    simp only [body,SourceProgram.toPhysical,toPhysical,PhysicalProgram.runReturns_prepend,
      NamedCircuit.toQuery,List.map_cons,List.map_nil,QueryCircuit.eval,one_mul]
    have hi := inserted_intertwines (Equiv.prodComm P Bool) b _ _
      (i.normalize_intertwines UA Ub b (fun h=>hb (by simp [hasPlain,h]))) v
    rw [hi]
    exact ih b (fun h=>hb (by simp [hasPlain,h])) _
  | measure i next ih =>
    simp only [body,SourceProgram.toPhysical,toPhysical,PhysicalProgram.runReturns]
    apply forall_congr'
    intro t
    have hm := measuredBit_inserted (Equiv.prodComm P Bool)
      (sourceEnableEmbedding (chart := chart)) b i (outcome t) v
    change measuredBit (enableCoordinates chart) (.inr i) (outcome t)*ᵥ
      inserted (Equiv.prodComm P Bool) b v = _ at hm
    rw [hm]
    apply ih
    intro h
    apply hb
    cases ht : outcome t <;> simp_all [hasPlain]
  | finish flag =>
    exact extendedLayout_returns (Equiv.prodComm P Bool) sourceEnableEmbedding F b v flag Pred hzero

theorem normalize_runDensity (F : TensorLayout chart dataChart) (c : AnyProgram chart a n)
    (UA : Matrix.unitaryGroup (Bits a × (Bits n ⊕ Bits n)) ℂ)
    (Ub : Matrix.unitaryGroup (Bits n ⊕ Bits n) ℂ) (select : Bool → Bool) (v : P → ℂ) :
    (c.normalize.toPhysical (enableLayout F)).runDensity TransducerCompiler.Physical.LocalGate.eval UA Ub select
      (inserted (Equiv.prodComm P Bool) false v)=
    (c.toPhysical F).runDensity TransducerCompiler.Physical.LocalGate.eval UA Ub select v := by
  by_cases hc : c.hasPlain=true
  · simp only [normalize,hc,ite_true,SourceProgram.toPhysical,PhysicalProgram.runDensity_prepend,
      SourceInstruction.sourceQuery,NamedCircuit.toQuery,List.map_cons,List.map_nil,
      NamedInstruction.toQuery,QueryCircuit.eval,QueryInstruction.eval,one_mul]
    have hi := congrArg (fun M=>M*ᵥv) (enableX_initializes chart)
    simp only [←Matrix.mulVec_mulVec] at hi
    change (enableX chart).eval.val*ᵥinserted (Equiv.prodComm P Bool) false v=
      inserted (Equiv.prodComm P Bool) true v at hi
    rw [hi]
    exact c.body_runDensity F UA Ub select true (fun _=>rfl) v
  · simp only [normalize,hc,ite_false]
    exact c.body_runDensity F UA Ub select false (fun h=>False.elim (hc h)) v

theorem normalize_runReturns (F : TensorLayout chart dataChart) (c : AnyProgram chart a n)
    (Pred : (Fin (Fintype.card D) → ℂ) → Prop) (hzero : Pred 0)
    (UA : Matrix.unitaryGroup (Bits a × (Bits n ⊕ Bits n)) ℂ)
    (Ub : Matrix.unitaryGroup (Bits n ⊕ Bits n) ℂ) (v : P → ℂ) :
    (c.normalize.toPhysical (enableLayout F)).runReturns Pred TransducerCompiler.Physical.LocalGate.eval UA Ub
      (inserted (Equiv.prodComm P Bool) false v) ↔
    (c.toPhysical F).runReturns Pred TransducerCompiler.Physical.LocalGate.eval UA Ub v := by
  by_cases hc : c.hasPlain=true
  · simp only [normalize,hc,ite_true,SourceProgram.toPhysical,PhysicalProgram.runReturns_prepend,
      SourceInstruction.sourceQuery,NamedCircuit.toQuery,List.map_cons,List.map_nil,
      NamedInstruction.toQuery,QueryCircuit.eval,QueryInstruction.eval,one_mul]
    have hi := congrArg (fun M=>M*ᵥv) (enableX_initializes chart)
    simp only [←Matrix.mulVec_mulVec] at hi
    change (enableX chart).eval.val*ᵥinserted (Equiv.prodComm P Bool) false v=
      inserted (Equiv.prodComm P Bool) true v at hi
    rw [hi]
    exact c.body_runReturns F Pred hzero UA Ub true (fun _=>rfl) v
  · simp only [normalize,hc,ite_false]
    exact c.body_runReturns F Pred hzero UA Ub false (fun h=>False.elim (hc h)) v

theorem normalize_executeDensity (F : TensorLayout chart dataChart) (c : AnyProgram chart a n)
    (UA : Matrix.unitaryGroup (Bits a × (Bits n ⊕ Bits n)) ℂ)
    (Ub : Matrix.unitaryGroup (Bits n ⊕ Bits n) ℂ) (select : Bool → Bool) (v : P → ℂ) :
    (c.normalize.lower (enableLayout F)).executeDensity UA Ub select
      (finiteVector (inserted (Equiv.prodComm P Bool) false v))=
    (c.lower F).executeDensity UA Ub select (finiteVector v) := by
  change ((c.normalize.toPhysical (enableLayout F)).lower _).executeDensity _ _ _ _ = _
  rw [PhysicalProgram.lower_runDensity,normalize_runDensity]
  exact (PhysicalProgram.lower_runDensity _ _ _ _ (c.toPhysical F) v).symm

theorem normalize_returns (F : TensorLayout chart dataChart) (c : AnyProgram chart a n)
    (Pred : (Fin (Fintype.card D) → ℂ) → Prop) (hzero : Pred 0)
    (UA : Matrix.unitaryGroup (Bits a × (Bits n ⊕ Bits n)) ℂ)
    (Ub : Matrix.unitaryGroup (Bits n ⊕ Bits n) ℂ) (v : P → ℂ) :
    Returns Pred UA Ub (c.normalize.lower (enableLayout F))
      (finiteVector (inserted (Equiv.prodComm P Bool) false v)) ↔
    Returns Pred UA Ub (c.lower F) (finiteVector v) := by
  change Returns _ _ _ ((c.normalize.toPhysical (enableLayout F)).lower _) _ ↔ _
  rw [PhysicalProgram.lower_runReturns,normalize_runReturns F c Pred hzero]
  exact (PhysicalProgram.lower_runReturns Pred _ _ _ (c.toPhysical F) v).symm

end AnyProgram
end OptimalQLS.Reduction.GenericSolver.Physical
