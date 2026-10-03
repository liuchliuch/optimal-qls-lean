import OptimalQLS.Reduction.GenericSolver.PhysicalMacros

/-! Uniform instruction/list substitution for any supplied physical solver.
There is no reference to the particular upper-bound Implementation. -/
noncomputable section
open scoped Classical
namespace OptimalQLS.Reduction.GenericSolver.Physical
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla LowerBounds
open Refinement.CostedExecution Preparation.CompilerAttachment
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
variable {P W : Type} [Fintype P] [DecidableEq P]
  {chart : P ≃ (W → Bool)} {a n : ℕ}

inductive SourceInstruction (chart : P ≃ (W → Bool)) (a n : ℕ) where
  | gate (g : TransducerCompiler.Physical.LocalGate chart)
  | matrix (F : MatrixFrame chart a n) (adj : Bool)
  | vector (F : VectorFrame chart n) (adj : Bool)

abbrev SourceCircuit (chart : P ≃ (W → Bool)) (a n : ℕ) := List (SourceInstruction chart a n)

def SourceInstruction.sourceQuery : SourceInstruction chart a n →
    NamedInstruction (TransducerCompiler.Physical.LocalGate chart)
      (Bits a × (Bits n ⊕ Bits n)) (Bits n ⊕ Bits n) P
  | .gate g => .gate g
  | .matrix F adj => .matrixCall F.port adj
  | .vector F adj => .vectorCall F.port adj

def instructionCode : SourceInstruction chart a n → Circuit chart a n
  | .gate g => [.gate (.old g)]
  | .matrix F adj => matrixCode F adj
  | .vector F adj => vectorCode F adj

def sourceCircuit (c : SourceCircuit chart a n) :
    NamedCircuit (TransducerCompiler.Physical.LocalGate chart)
      (Bits a × (Bits n ⊕ Bits n)) (Bits n ⊕ Bits n) P := c.map SourceInstruction.sourceQuery

def substitute (c : SourceCircuit chart a n) : Circuit chart a n := c.flatMap instructionCode

def SourceInstruction.work : SourceInstruction chart a n → ℕ
  | .gate _ => 1
  | _ => 0
def SourceInstruction.matrixCalls : SourceInstruction chart a n → ℕ
  | .matrix _ _ => 1
  | _ => 0
def SourceInstruction.vectorCalls : SourceInstruction chart a n → ℕ
  | .vector _ _ => 1
  | _ => 0

theorem instructionCode_counts (i : SourceInstruction chart a n) :
    ((instructionCode i).toQuery gateEval).matrixQueries=2*i.matrixCalls ∧
    ((instructionCode i).toQuery gateEval).vectorQueries=i.vectorCalls ∧
    (instructionCode i).workGates≤ i.work + 4801*i.matrixCalls := by
  cases i with
  | gate g => simp [instructionCode,SourceInstruction.matrixCalls,SourceInstruction.vectorCalls,
      SourceInstruction.work,NamedCircuit.toQuery,NamedInstruction.toQuery,
      QueryCircuit.matrixQueries,QueryCircuit.vectorQueries,NamedCircuit.workGates]
  | matrix F adj => simpa [instructionCode,SourceInstruction.matrixCalls,
      SourceInstruction.vectorCalls,SourceInstruction.work] using matrixCode_counts F adj
  | vector F adj =>
    have h := vectorCode_counts (a := a) F adj
    exact ⟨h.1,h.2.1,h.2.2.le⟩

theorem instructionCode_intertwines (i : SourceInstruction chart a n)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    (((instructionCode i).toQuery gateEval).eval UA Ub).val*basisInsertion clean =
      basisInsertion clean *
        ((i.sourceQuery.toQuery TransducerCompiler.Physical.LocalGate.eval).eval
          (dilationEncoding UA) (preparation Ub)).val := by
  cases i with
  | gate g =>
    simpa [instructionCode,SourceInstruction.sourceQuery,NamedCircuit.toQuery,
      NamedInstruction.toQuery,QueryCircuit.eval,QueryInstruction.eval,gateEval,clean] using
      scratchPort_intertwines (Equiv.refl (P × PhaseScratch)) (false,false,false) g.eval
  | matrix F adj => exact matrixCode_intertwines F adj UA Ub
  | vector F adj => exact vectorCode_intertwines F adj UA Ub

theorem substitute_counts (c : SourceCircuit chart a n) :
    ((substitute c).toQuery gateEval).matrixQueries=
      2*((sourceCircuit c).toQuery TransducerCompiler.Physical.LocalGate.eval).matrixQueries ∧
    ((substitute c).toQuery gateEval).vectorQueries=
      ((sourceCircuit c).toQuery TransducerCompiler.Physical.LocalGate.eval).vectorQueries ∧
    (substitute c).workGates≤(sourceCircuit c).workGates+
      4801*((sourceCircuit c).toQuery TransducerCompiler.Physical.LocalGate.eval).matrixQueries := by
  induction c with
  | nil => exact ⟨rfl,rfl,by simp [substitute,sourceCircuit,NamedCircuit.workGates,
      NamedCircuit.toQuery,QueryCircuit.matrixQueries]⟩
  | cons i c ih =>
    have hi := instructionCode_counts i
    change (((instructionCode i)++substitute c).toQuery _).matrixQueries=_ ∧
      (((instructionCode i)++substitute c).toQuery _).vectorQueries=_ ∧
      ((instructionCode i)++substitute c).workGates≤_
    simp only [NamedCircuit.toQuery_append,QueryCircuit.matrixQueries_append,
      QueryCircuit.vectorQueries_append,NamedCircuit.workGates_append]
    cases i <;>
      simp only [sourceCircuit,List.map_cons,SourceInstruction.sourceQuery,
        NamedCircuit.toQuery,NamedInstruction.toQuery,QueryCircuit.matrixQueries,
        QueryCircuit.vectorQueries,NamedCircuit.workGates,SourceInstruction.matrixCalls,
        SourceInstruction.vectorCalls,SourceInstruction.work] at * <;> omega

theorem substitute_intertwines (c : SourceCircuit chart a n)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    (((substitute c).toQuery gateEval).eval UA Ub).val*basisInsertion clean =
      basisInsertion clean *
        (((sourceCircuit c).toQuery TransducerCompiler.Physical.LocalGate.eval).eval
          (dilationEncoding UA) (preparation Ub)).val := by
  induction c with
  | nil => simp [substitute,sourceCircuit,NamedCircuit.toQuery,QueryCircuit.eval]
  | cons i c ih =>
    have hh := intertwines_mul (basisInsertion clean) _ _ _ _
      (instructionCode_intertwines i UA Ub) ih
    simpa only [substitute,sourceCircuit,List.flatMap_cons,List.map_cons,
      NamedCircuit.toQuery,List.map_append,List.map_cons,QueryCircuit.eval_append,
      QueryCircuit.eval,Submonoid.coe_mul] using hh

/-- In particular this intertwining is an equality on every coherent input,
not just the one promised solver input. -/
theorem substitute_apply (c : SourceCircuit chart a n)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (v : P → ℂ) :
    (((substitute c).toQuery gateEval).eval UA Ub).val*ᵥ(basisInsertion clean*ᵥv)=
      basisInsertion clean*ᵥ
        ((((sourceCircuit c).toQuery TransducerCompiler.Physical.LocalGate.eval).eval
          (dilationEncoding UA) (preparation Ub)).val*ᵥv) := by
  simpa only [Matrix.mulVec_mulVec] using congrArg (fun M=>M*ᵥv) (substitute_intertwines c UA Ub)

end OptimalQLS.Reduction.GenericSolver.Physical
