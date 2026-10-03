import OptimalQLS.Reduction.GenericSolver.PhysicalNormalizeCalls
import OptimalQLS.Reduction.GenericSolver.PhysicalExecution

/-! A branching solver may contain both ordinary and single-control calls.
Normalization adds at most one unitary gate for the entire run and preserves
both query counters and every measurement branch. -/
noncomputable section
open scoped Classical BigOperators
namespace OptimalQLS.Reduction.GenericSolver.Physical
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla LowerBounds
open Refinement.CostedExecution Refinement.PhysicalMeasurement Preparation.CompilerAttachment
open FreshCopies
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
variable {P W : Type} [Fintype P] [DecidableEq P]
  {chart : P ≃ (W → Bool)} {a n : ℕ}

inductive AnyProgram (chart : P ≃ (W → Bool)) (a n : ℕ) where
  | step (i : AnyInstruction chart a n) (next : AnyProgram chart a n)
  | measure (i : W) (next : Bool → AnyProgram chart a n)
  | finish (success : Bool)

namespace AnyProgram

def work : AnyProgram chart a n → ℕ
  | .step i next => i.work+next.work
  | .measure _ next => max (next false).work (next true).work
  | .finish _ => 0
def measurements : AnyProgram chart a n → ℕ
  | .step _ next => next.measurements
  | .measure _ next => max (next false).measurements (next true).measurements+1
  | .finish _ => 0
def matrixCalls : AnyProgram chart a n → ℕ
  | .step i next => i.matrixCalls+next.matrixCalls
  | .measure _ next => max (next false).matrixCalls (next true).matrixCalls
  | .finish _ => 0
def vectorCalls : AnyProgram chart a n → ℕ
  | .step i next => i.vectorCalls+next.vectorCalls
  | .measure _ next => max (next false).vectorCalls (next true).vectorCalls
  | .finish _ => 0
def hasPlain : AnyProgram chart a n → Bool
  | .step i next => i.isPlain || next.hasPlain
  | .measure _ next => (next false).hasPlain || (next true).hasPlain
  | .finish _ => false

def body : AnyProgram chart a n → SourceProgram (enableCoordinates chart) a n
  | .step i next => .step i.normalize next.body
  | .measure i next => .measure (.inr i) (fun b=>(next b).body)
  | .finish flag => .finish flag

def initializationCost (c : AnyProgram chart a n) : ℕ := if c.hasPlain then 1 else 0

def normalize (c : AnyProgram chart a n) : SourceProgram (enableCoordinates chart) a n :=
  if c.hasPlain then .step (.gate (enableX chart)) c.body else c.body

theorem body_counts (c : AnyProgram chart a n) :
    c.body.work=c.work ∧ c.body.measurements=c.measurements ∧
    c.body.matrixCalls=c.matrixCalls ∧ c.body.vectorCalls=c.vectorCalls := by
  induction c with
  | step i next ih =>
    rcases ih with ⟨hw,hm,hA,hB⟩
    rcases i.normalize_counts with ⟨hiw,hiA,hiB⟩
    simp [body,SourceProgram.work,SourceProgram.measurements,SourceProgram.matrixCalls,
      SourceProgram.vectorCalls,work,measurements,matrixCalls,vectorCalls,hw,hm,hA,hB,hiw,hiA,hiB]
  | measure i next ih =>
    rcases ih false with ⟨hwf,hmf,hAf,hBf⟩
    rcases ih true with ⟨hwt,hmt,hAt,hBt⟩
    simp [body,SourceProgram.work,SourceProgram.measurements,SourceProgram.matrixCalls,
      SourceProgram.vectorCalls,work,measurements,matrixCalls,vectorCalls,hwf,hmf,hAf,hBf,hwt,hmt,hAt,hBt]
  | finish flag => exact ⟨rfl,rfl,rfl,rfl⟩

theorem normalize_counts (c : AnyProgram chart a n) :
    c.normalize.work=c.work+c.initializationCost ∧
    c.normalize.measurements=c.measurements ∧
    c.normalize.matrixCalls=c.matrixCalls ∧ c.normalize.vectorCalls=c.vectorCalls := by
  rcases body_counts c with ⟨hw,hm,hA,hB⟩
  by_cases hc : c.hasPlain=true <;>
    simp [normalize,initializationCost,hc,SourceProgram.work,SourceProgram.measurements,
      SourceProgram.matrixCalls,SourceProgram.vectorCalls,SourceInstruction.work,
      SourceInstruction.matrixCalls,SourceInstruction.vectorCalls,hw,hm,hA,hB,Nat.add_comm]

theorem hasPlain_positive (c : AnyProgram chart a n) (h : c.hasPlain=true) :
    0<c.matrixCalls+c.vectorCalls := by
  induction c with
  | step i next ih =>
    simp only [hasPlain,Bool.or_eq_true] at h
    rcases h with hi|hn
    · cases i with
      | core i => cases hi
      | matrix F adj => simp [matrixCalls,vectorCalls,AnyInstruction.matrixCalls,AnyInstruction.vectorCalls]
      | vector F adj => simp [matrixCalls,vectorCalls,AnyInstruction.matrixCalls,AnyInstruction.vectorCalls]
    · have hn' := ih hn
      simp only [matrixCalls,vectorCalls]
      omega
  | measure i next ih =>
    simp only [hasPlain,Bool.or_eq_true] at h
    rcases h with hf|ht
    · have hh := ih false hf
      simp only [matrixCalls,vectorCalls]
      omega
    · have hh := ih true ht
      simp only [matrixCalls,vectorCalls]
      omega
  | finish flag => cases h

theorem initializationCost_le_queries (c : AnyProgram chart a n) :
    c.initializationCost≤c.matrixCalls+c.vectorCalls := by
  by_cases hc : c.hasPlain=true
  · have h := c.hasPlain_positive hc
    simp only [initializationCost,hc,ite_true]
    omega
  · simp [initializationCost,hc]

variable {D V : Type} [Fintype D] [DecidableEq D] {dataChart : D ≃ (V → Bool)}

def toPhysical (F : TensorLayout chart dataChart) : AnyProgram chart a n →
    PhysicalProgram (TransducerCompiler.Physical.LocalGate chart)
      (Bits a × (Bits n ⊕ Bits n)) (Bits n ⊕ Bits n) chart dataChart
  | .step i next => PhysicalProgram.prepend [i.sourceQuery] (next.toPhysical F)
  | .measure i next => .measure i (fun b=>(next b).toPhysical F)
  | .finish flag => .finish F flag

def lower (F : TensorLayout chart dataChart) (c : AnyProgram chart a n) :=
  (c.toPhysical F).lower TransducerCompiler.Physical.LocalGate.eval

end AnyProgram

def enableLayout {D V : Type} [Fintype D] [DecidableEq D] {dataChart : D ≃ (V → Bool)}
    (F : TensorLayout chart dataChart) : TensorLayout (enableCoordinates chart) dataChart where
  Rest := F.Rest × Bool
  frame := tensorFrame F.frame (Equiv.prodComm P Bool)
  wires := F.wires.comp sourceEnableEmbedding

end OptimalQLS.Reduction.GenericSolver.Physical
