import OptimalQLS.Reduction.GenericSolver.PhysicalEnable

/-! Optional-control calls normalize to the core single-control syntax with
one enable initialization for the whole run, only when a plain call exists. -/
noncomputable section
open scoped Classical
namespace OptimalQLS.Reduction.GenericSolver.Physical
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla LowerBounds
open Refinement.CostedExecution Preparation.CompilerAttachment
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
variable {P W : Type} [Fintype P] [DecidableEq P]
  {chart : P ≃ (W → Bool)} {a n : ℕ}

inductive AnyInstruction (chart : P ≃ (W → Bool)) (a n : ℕ) where
  | core (i : SourceInstruction chart a n)
  | matrix (F : PlainMatrixFrame chart a n) (adj : Bool)
  | vector (F : PlainVectorFrame chart n) (adj : Bool)

def AnyInstruction.isPlain : AnyInstruction chart a n → Bool
  | .core _ => false
  | _ => true

def AnyInstruction.sourceQuery : AnyInstruction chart a n →
    NamedInstruction (TransducerCompiler.Physical.LocalGate chart)
      (Bits a × (Bits n ⊕ Bits n)) (Bits n ⊕ Bits n) P
  | .core i => i.sourceQuery
  | .matrix F adj => .matrixCall (scratchPort F.frame) adj
  | .vector F adj => .vectorCall (scratchPort F.frame) adj

def AnyInstruction.normalize : AnyInstruction chart a n → SourceInstruction (enableCoordinates chart) a n
  | .core i => liftInstruction i
  | .matrix F adj => .matrix F.controlled adj
  | .vector F adj => .vector F.controlled adj

def AnyInstruction.work : AnyInstruction chart a n → ℕ
  | .core i => i.work
  | _ => 0
def AnyInstruction.matrixCalls : AnyInstruction chart a n → ℕ
  | .core i => i.matrixCalls
  | .matrix _ _ => 1
  | .vector _ _ => 0
def AnyInstruction.vectorCalls : AnyInstruction chart a n → ℕ
  | .core i => i.vectorCalls
  | .matrix _ _ => 0
  | .vector _ _ => 1

theorem AnyInstruction.normalize_counts (i : AnyInstruction chart a n) :
    i.normalize.work=i.work ∧ i.normalize.matrixCalls=i.matrixCalls ∧
      i.normalize.vectorCalls=i.vectorCalls := by
  cases i with
  | core i => exact liftInstruction_counts i
  | matrix F adj => exact ⟨rfl,rfl,rfl⟩
  | vector F adj => exact ⟨rfl,rfl,rfl⟩

theorem AnyInstruction.normalize_intertwines (i : AnyInstruction chart a n)
    (UA : Matrix.unitaryGroup (Bits a × (Bits n ⊕ Bits n)) ℂ)
    (Ub : Matrix.unitaryGroup (Bits n ⊕ Bits n) ℂ) (b : Bool)
    (hb : i.isPlain=true → b=true) :
    ((i.normalize.sourceQuery.toQuery TransducerCompiler.Physical.LocalGate.eval).eval UA Ub).val *
      basisInsertion (fun x : P => (b,x)) =
      basisInsertion (fun x : P => (b,x)) *
        ((i.sourceQuery.toQuery TransducerCompiler.Physical.LocalGate.eval).eval UA Ub).val := by
  cases i with
  | core i => exact liftInstruction_intertwines i UA Ub b
  | matrix F adj =>
    have hb' : b=true := hb rfl
    subst b
    change (F.controlled.port.apply (if adj then UA⁻¹ else UA)).val*basisInsertion enabled =
      basisInsertion enabled*((scratchPort F.frame).apply (if adj then UA⁻¹ else UA)).val
    rw [MatrixFrame.port_apply,scratchPort_apply]
    exact enabledFrame_intertwines F.frame _
  | vector F adj =>
    have hb' : b=true := hb rfl
    subst b
    change (F.controlled.port.apply (if adj then Ub⁻¹ else Ub)).val*basisInsertion enabled =
      basisInsertion enabled*((scratchPort F.frame).apply (if adj then Ub⁻¹ else Ub)).val
    rw [VectorFrame.port_apply,scratchPort_apply]
    exact enabledFrame_intertwines F.frame _

end OptimalQLS.Reduction.GenericSolver.Physical
