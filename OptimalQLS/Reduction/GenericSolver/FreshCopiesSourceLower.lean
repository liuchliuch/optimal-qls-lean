import OptimalQLS.Reduction.GenericSolver.FreshCopiesSyntax

/-! The arbitrary source solver's literal tree, output-factor partial trace,
and separate syntactic resources. -/
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
  {chart : P ≃ (W → Bool)} {dataChart : D ≃ (V → Bool)}

namespace PhysicalProgram
variable {G : Type*} {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

theorem lower_prepend (gate : G → Matrix.unitaryGroup P ℂ) (c : NamedCircuit G A B P)
    (next : PhysicalProgram G A B chart dataChart) :
    (prepend c next).lower gate=
      Refinement.Repetition.prepend
        (Refinement.Repetition.reindexCircuit (Fintype.equivFin P) (c.toQuery gate)) (next.lower gate) := by
  induction c with
  | nil => rfl
  | cons i c ih =>
    cases i <;> simp only [prepend,lower,NamedCircuit.toQuery,NamedInstruction.toQuery,
      List.map_cons,Refinement.Repetition.reindexCircuit,Refinement.Repetition.reindexInstruction,
      Refinement.Repetition.prepend] at ih ⊢ <;> rw [ih]

end PhysicalProgram

namespace SourceProgram
variable {a n : ℕ}

def toPhysical (F : TensorLayout chart dataChart) : SourceProgram chart a n →
    PhysicalProgram (TransducerCompiler.Physical.LocalGate chart)
      (Bits a × (Bits n ⊕ Bits n)) (Bits n ⊕ Bits n) chart dataChart
  | .step i next => PhysicalProgram.prepend [i.sourceQuery] (next.toPhysical F)
  | .measure i next => .measure i (fun b=>(next b).toPhysical F)
  | .finish flag => .finish F flag

def lower (F : TensorLayout chart dataChart) (c : SourceProgram chart a n) :
    FiniteOracleProgram (Bits a × (Bits n ⊕ Bits n)) (Bits n ⊕ Bits n)
      (Fintype.card D) (Fintype.card P) :=
  (c.toPhysical F).lower TransducerCompiler.Physical.LocalGate.eval

theorem lower_step (F : TensorLayout chart dataChart) (i : SourceInstruction chart a n)
    (next : SourceProgram chart a n) :
    (SourceProgram.step i next).lower F=
      Refinement.Repetition.prepend
        (Refinement.Repetition.reindexCircuit (Fintype.equivFin P)
          [i.sourceQuery.toQuery TransducerCompiler.Physical.LocalGate.eval]) (next.lower F) :=
  PhysicalProgram.lower_prepend _ _ _

theorem toPhysical_work (F : TensorLayout chart dataChart) (c : SourceProgram chart a n) :
    (c.toPhysical F).work=c.work := by
  induction c with
  | step i next ih => cases i <;>
      simp [toPhysical,PhysicalProgram.prepend,PhysicalProgram.work,work,
        SourceInstruction.sourceQuery,SourceInstruction.work,ih,Nat.add_comm]
  | measure i next ih => simp [toPhysical,PhysicalProgram.work,work,ih]
  | finish flag => rfl

theorem toPhysical_measurements (F : TensorLayout chart dataChart) (c : SourceProgram chart a n) :
    (c.toPhysical F).measurements=c.measurements := by
  induction c with
  | step i next ih => cases i <;>
      simp [toPhysical,PhysicalProgram.prepend,PhysicalProgram.measurements,measurements,
        SourceInstruction.sourceQuery,ih]
  | measure i next ih => simp [toPhysical,PhysicalProgram.measurements,measurements,ih]
  | finish flag => rfl

theorem toPhysical_matrixCalls (F : TensorLayout chart dataChart) (c : SourceProgram chart a n) :
    (c.toPhysical F).matrixCalls=c.matrixCalls := by
  induction c with
  | step i next ih => cases i <;>
      simp [toPhysical,PhysicalProgram.prepend,PhysicalProgram.matrixCalls,matrixCalls,
        SourceInstruction.sourceQuery,SourceInstruction.matrixCalls,ih,Nat.add_comm]
  | measure i next ih => simp [toPhysical,PhysicalProgram.matrixCalls,matrixCalls,ih]
  | finish flag => rfl

theorem toPhysical_vectorCalls (F : TensorLayout chart dataChart) (c : SourceProgram chart a n) :
    (c.toPhysical F).vectorCalls=c.vectorCalls := by
  induction c with
  | step i next ih => cases i <;>
      simp [toPhysical,PhysicalProgram.prepend,PhysicalProgram.vectorCalls,vectorCalls,
        SourceInstruction.sourceQuery,SourceInstruction.vectorCalls,ih,Nat.add_comm]
  | measure i next ih => simp [toPhysical,PhysicalProgram.vectorCalls,vectorCalls,ih]
  | finish flag => rfl

end SourceProgram
end OptimalQLS.Reduction.GenericSolver.FreshCopies
