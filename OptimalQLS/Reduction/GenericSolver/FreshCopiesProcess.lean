import OptimalQLS.Refinement.CostedExecution.AdapterQueryLocalityFilterDirectCore
import OptimalQLS.Reduction.GenericSolver.FreshCopiesRegisters

/-! A fully physical tree with shrinking registers. Traces discard literal
wire factors and perform no unitary gates; all fresh registers already exist
in the input. This permits retries without a workspace-sized reset circuit. -/
noncomputable section
open scoped Classical BigOperators
namespace OptimalQLS.Reduction.GenericSolver.FreshCopies
open Matrix TransducerCompiler PolynomialTransform
open Refinement.CostedExecution
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

variable {A B VA VB : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

inductive Process (argumentsA : A ≃ (VA → Bool)) (argumentsB : B ≃ (VB → Bool))
    (output : Register) : Register → Type 1 where
  | unitary {R : Register} (U : Matrix.unitaryGroup R.State ℂ)
      (locality : IsTwoLocal R.bits U) (next : Process argumentsA argumentsB output R) :
      Process argumentsA argumentsB output R
  | matrix {R : Register} (p : QueryPort A R.State) (adj : Bool)
      (placement : LiteralQueryPlacement argumentsA R.bits p)
      (next : Process argumentsA argumentsB output R) : Process argumentsA argumentsB output R
  | vector {R : Register} (p : QueryPort B R.State) (adj : Bool)
      (placement : LiteralQueryPlacement argumentsB R.bits p)
      (next : Process argumentsA argumentsB output R) : Process argumentsA argumentsB output R
  | measure {R : Register} (i : R.Wire) (next : Bool → Process argumentsA argumentsB output R) :
      Process argumentsA argumentsB output R
  | trace {R Q : Register} (layout : TensorLayout R.bits Q.bits)
      (next : Process argumentsA argumentsB output Q) : Process argumentsA argumentsB output R
  | output (success : Bool) : Process argumentsA argumentsB output output

namespace Process
variable {argumentsA : A ≃ (VA → Bool)} {argumentsB : B ≃ (VB → Bool)} {O R : Register}

def work : {R : Register} → Process argumentsA argumentsB O R → ℕ
  | _,.unitary _ _ next => next.work+1
  | _,.matrix _ _ _ next => next.work
  | _,.vector _ _ _ next => next.work
  | _,.measure _ next => max (next false).work (next true).work
  | _,.trace _ next => next.work
  | _,.output _ => 0

def measurements : {R : Register} → Process argumentsA argumentsB O R → ℕ
  | _,.unitary _ _ next => next.measurements
  | _,.matrix _ _ _ next => next.measurements
  | _,.vector _ _ _ next => next.measurements
  | _,.measure _ next => max (next false).measurements (next true).measurements+1
  | _,.trace _ next => next.measurements
  | _,.output _ => 0

def matrixCalls : {R : Register} → Process argumentsA argumentsB O R → ℕ
  | _,.unitary _ _ next => next.matrixCalls
  | _,.matrix _ _ _ next => next.matrixCalls+1
  | _,.vector _ _ _ next => next.matrixCalls
  | _,.measure _ next => max (next false).matrixCalls (next true).matrixCalls
  | _,.trace _ next => next.matrixCalls
  | _,.output _ => 0

def vectorCalls : {R : Register} → Process argumentsA argumentsB O R → ℕ
  | _,.unitary _ _ next => next.vectorCalls
  | _,.matrix _ _ _ next => next.vectorCalls
  | _,.vector _ _ _ next => next.vectorCalls+1
  | _,.measure _ next => max (next false).vectorCalls (next true).vectorCalls
  | _,.trace _ next => next.vectorCalls
  | _,.output _ => 0

def lower : {R : Register} → Process argumentsA argumentsB O R →
    LowerBounds.FiniteOracleProgram A B O.dimension R.dimension
  | R,.unitary U _ next => .instrument 1 (fun _=>R.dimension)
      (fun _=>(rewireUnitary R.index U).val)
      (by rw [Fin.sum_univ_one];exact (rewireUnitary R.index U).property.1) (fun _=>next.lower)
  | R,.matrix p adj _ next => .matrixQuery (Refinement.Repetition.reindexPort R.index p) adj next.lower
  | R,.vector p adj _ next => .vectorQuery (Refinement.Repetition.reindexPort R.index p) adj next.lower
  | R,.measure i next => .instrument 2 (fun _=>R.dimension)
      (fun b=>indexedMatrix R R (measuredBit R.bits i (outcome b)))
      (indexedMatrix_normalized R R _ (measuredBit_normalized R.bits i))
      (fun b=>(next (outcome b)).lower)
  | _,.trace F next => .instrument (Fintype.card F.Rest) (fun _=>_) F.indexedKraus
      F.indexedKraus_normalized (fun _=>next.lower)
  | _,.output flag => .output flag false

/-- Literal right-hand spectator register, with every physical argument wire
and every unselected bit preserved. -/
def tensor (T : Register) : {R : Register} → Process argumentsA argumentsB O R →
    Process argumentsA argumentsB (O.product T) (R.product T)
  | R,.unitary U hl next => .unitary (GateSynthesis.placeHom (Equiv.refl _) U)
      (IsTwoLocal.place _ (Register.firstEmbedding R T) _ hl) (next.tensor T)
  | R,.matrix p adj L next =>
    .matrix ((scratchPort (Equiv.refl (R.State × T.State))).comp p) adj
      { frame := Refinement.CostedExecution.ControlFrame.direct_lift L.frame (Equiv.refl _)
        wires := L.wires.comp (Register.firstEmbedding R T) } (next.tensor T)
  | R,.vector p adj L next =>
    .vector ((scratchPort (Equiv.refl (R.State × T.State))).comp p) adj
      { frame := Refinement.CostedExecution.ControlFrame.direct_lift L.frame (Equiv.refl _)
        wires := L.wires.comp (Register.firstEmbedding R T) } (next.tensor T)
  | _,.measure i next => .measure (.inl i) (fun b=>(next b).tensor T)
  | _,.trace F next => .trace (F.product T) (next.tensor T)
  | _,.output flag => .output flag

theorem tensor_resources (T : Register) (p : Process argumentsA argumentsB O R) :
    (p.tensor T).work=p.work ∧ (p.tensor T).measurements=p.measurements ∧
      (p.tensor T).matrixCalls=p.matrixCalls ∧ (p.tensor T).vectorCalls=p.vectorCalls := by
  induction p with
  | unitary U h next ih => simp [tensor,work,measurements,matrixCalls,vectorCalls,ih]
  | matrix p adj L next ih => simp [tensor,work,measurements,matrixCalls,vectorCalls,ih]
  | vector p adj L next ih => simp [tensor,work,measurements,matrixCalls,vectorCalls,ih]
  | measure i next ih => simp [tensor,work,measurements,matrixCalls,vectorCalls,ih]
  | trace F next ih => exact ih
  | output flag => exact ⟨rfl,rfl,rfl,rfl⟩

end Process
end OptimalQLS.Reduction.GenericSolver.FreshCopies
