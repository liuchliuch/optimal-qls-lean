import OptimalQLS.Reduction.GenericSolver.FreshCopiesSource

/-! Physical branching syntax with only local unitary leaves, literal bit
measurements and literal output-factor discard. Output wire selection may
vary with the classical branch without moving quantum data. -/
noncomputable section
open scoped Classical BigOperators
namespace OptimalQLS.Reduction.GenericSolver.FreshCopies
open Matrix LowerBounds PolynomialTransform TransducerCompiler
open Refinement.CostedExecution
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

variable {P W D V : Type} [Fintype P] [DecidableEq P] [Fintype D] [DecidableEq D]

def finiteMatrix (M : Matrix D P ℂ) : Matrix (Fin (Fintype.card D)) (Fin (Fintype.card P)) ℂ :=
  M.submatrix (Fintype.equivFin D).symm (Fintype.equivFin P).symm

theorem finiteMatrix_normalized {I : Type} [Fintype I] (K : I → Matrix D P ℂ)
    (hn : ∑ i,(K i)ᴴ*K i=1) :
    ∑ i,(finiteMatrix (K i))ᴴ*finiteMatrix (K i)=1 := by
  simp_rw [finiteMatrix,Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv]
  have hs : (∑ i,((K i)ᴴ*K i).submatrix (Fintype.equivFin P).symm (Fintype.equivFin P).symm)=
      (∑ i,(K i)ᴴ*K i).submatrix (Fintype.equivFin P).symm (Fintype.equivFin P).symm := by
    ext x y
    simp only [Matrix.sum_apply,Matrix.submatrix_apply]
  rw [hs,hn,Matrix.submatrix_one_equiv]

variable {chart : P ≃ (W → Bool)} {dataChart : D ≃ (V → Bool)}

theorem TensorLayout.finite_kraus_normalized (F : TensorLayout chart dataChart) :
    ∑ i : Fin (Fintype.card F.Rest),
      (finiteMatrix (F.kraus ((Fintype.equivFin F.Rest).symm i)))ᴴ*
        finiteMatrix (F.kraus ((Fintype.equivFin F.Rest).symm i))=1 := by
  rw [(Fintype.equivFin F.Rest).symm.sum_comp
    (fun r=>(finiteMatrix (F.kraus r))ᴴ*finiteMatrix (F.kraus r))]
  exact finiteMatrix_normalized F.kraus F.kraus_normalized

inductive PhysicalProgram (G : Type*) (A B : Type) (chart : P ≃ (W → Bool)) (dataChart : D ≃ (V → Bool)) where
  | named (g : G) (next : PhysicalProgram G A B chart dataChart)
  | matrix (p : QueryPort A P) (adj : Bool) (next : PhysicalProgram G A B chart dataChart)
  | vector (p : QueryPort B P) (adj : Bool) (next : PhysicalProgram G A B chart dataChart)
  | measure (i : W) (next : Bool → PhysicalProgram G A B chart dataChart)
  | finish (layout : TensorLayout chart dataChart) (success : Bool)

namespace PhysicalProgram
variable {G : Type*} {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def work : PhysicalProgram G A B chart dataChart → ℕ
  | .named _ next => next.work+1
  | .matrix _ _ next => next.work
  | .vector _ _ next => next.work
  | .measure _ next => max (next false).work (next true).work
  | .finish _ _ => 0

def measurements : PhysicalProgram G A B chart dataChart → ℕ
  | .named _ next => next.measurements
  | .matrix _ _ next => next.measurements
  | .vector _ _ next => next.measurements
  | .measure _ next => max (next false).measurements (next true).measurements+1
  | .finish _ _ => 0

def matrixCalls : PhysicalProgram G A B chart dataChart → ℕ
  | .named _ next => next.matrixCalls
  | .matrix _ _ next => next.matrixCalls+1
  | .vector _ _ next => next.matrixCalls
  | .measure _ next => max (next false).matrixCalls (next true).matrixCalls
  | .finish _ _ => 0

def vectorCalls : PhysicalProgram G A B chart dataChart → ℕ
  | .named _ next => next.vectorCalls
  | .matrix _ _ next => next.vectorCalls
  | .vector _ _ next => next.vectorCalls+1
  | .measure _ next => max (next false).vectorCalls (next true).vectorCalls
  | .finish _ _ => 0

def lower (gate : G → Matrix.unitaryGroup P ℂ) : PhysicalProgram G A B chart dataChart →
    FiniteOracleProgram A B (Fintype.card D) (Fintype.card P)
  | .named g next => .instrument 1 (fun _=>Fintype.card P)
      (fun _=>(rewireUnitary (Fintype.equivFin P) (gate g)).val)
      (by rw [Fin.sum_univ_one]; exact (rewireUnitary (Fintype.equivFin P) (gate g)).property.1)
      (fun _=>next.lower gate)
  | .matrix p adj next => .matrixQuery (Refinement.Repetition.reindexPort (Fintype.equivFin P) p) adj
      (next.lower gate)
  | .vector p adj next => .vectorQuery (Refinement.Repetition.reindexPort (Fintype.equivFin P) p) adj
      (next.lower gate)
  | .measure i next => .instrument 2 (fun _=>Fintype.card P)
      (fun b=>finiteMatrix (measuredBit chart i (outcome b)))
      (finiteMatrix_normalized _ (measuredBit_normalized chart i))
      (fun b=>(next (outcome b)).lower gate)
  | .finish F flag => .instrument (Fintype.card F.Rest) (fun _=>Fintype.card D)
      (fun i=>finiteMatrix (F.kraus ((Fintype.equivFin F.Rest).symm i)))
      F.finite_kraus_normalized (fun _=>.output flag false)

def prepend (c : NamedCircuit G A B P) (next : PhysicalProgram G A B chart dataChart) :
    PhysicalProgram G A B chart dataChart :=
  match c with
  | [] => next
  | .gate g::c => .named g (prepend c next)
  | .matrixCall p b::c => .matrix p b (prepend c next)
  | .vectorCall p b::c => .vector p b (prepend c next)

theorem prepend_work (c : NamedCircuit G A B P) (next : PhysicalProgram G A B chart dataChart) :
    (prepend c next).work=c.workGates+next.work := by
  induction c with
  | nil => simp [prepend,NamedCircuit.workGates,NamedCircuit.toQuery,QueryCircuit.matrixQueries,QueryCircuit.vectorQueries]
  | cons i c ih => cases i <;> simp [prepend,work,NamedCircuit.workGates,ih,Nat.add_assoc,Nat.add_comm]

theorem prepend_matrixCalls (gate : G → Matrix.unitaryGroup P ℂ) (c : NamedCircuit G A B P)
    (next : PhysicalProgram G A B chart dataChart) :
    (prepend c next).matrixCalls=(c.toQuery gate).matrixQueries+next.matrixCalls := by
  induction c with
  | nil => simp [prepend,NamedCircuit.workGates,NamedCircuit.toQuery,QueryCircuit.matrixQueries,QueryCircuit.vectorQueries]
  | cons i c ih => cases i <;> simp [prepend,matrixCalls,NamedCircuit.toQuery,
      NamedInstruction.toQuery,QueryCircuit.matrixQueries,ih,Nat.add_assoc,Nat.add_comm]

theorem prepend_vectorCalls (gate : G → Matrix.unitaryGroup P ℂ) (c : NamedCircuit G A B P)
    (next : PhysicalProgram G A B chart dataChart) :
    (prepend c next).vectorCalls=(c.toQuery gate).vectorQueries+next.vectorCalls := by
  induction c with
  | nil => simp [prepend,NamedCircuit.workGates,NamedCircuit.toQuery,QueryCircuit.matrixQueries,QueryCircuit.vectorQueries]
  | cons i c ih => cases i <;> simp [prepend,vectorCalls,NamedCircuit.toQuery,
      NamedInstruction.toQuery,QueryCircuit.vectorQueries,ih,Nat.add_assoc,Nat.add_comm]

end PhysicalProgram
end OptimalQLS.Reduction.GenericSolver.FreshCopies
