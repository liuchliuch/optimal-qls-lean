import OptimalQLS.Refinement.CostedExecution.Primitives
import OptimalQLS.Reduction.GenericSolver.PhysicalSubstitution
import OptimalQLS.Reduction.GenericSolver.FreshCopiesTensor

/-! An arbitrary supplied physical solver with literal local instructions,
one-bit measurements and a chosen output tensor factor. Classical branching
never assumes a single pure successful aggregate state. -/
noncomputable section
open scoped Classical BigOperators
namespace OptimalQLS.Reduction.GenericSolver.FreshCopies
open Matrix LowerBounds PolynomialTransform TransducerCompiler BinaryClock
open Refinement.CostedExecution Physical
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

variable {P W : Type} [Fintype P] [DecidableEq P]

def sumCoordinates (n : ℕ) : (Bits n ⊕ Bits n) ≃ (Fin (n+1) → Bool) :=
  PhysicalAdapter.sumBits n |>.symm

/-- Only a literal data factor may be returned. The other physical wires are
traced out; the coordinate witness is not a gate or a unitary permutation. -/
structure TensorLayout {D V : Type} (chart : P ≃ (W → Bool)) (dataChart : D ≃ (V → Bool)) where
  Rest : Type
  [finiteRest : Fintype Rest]
  [decidableRest : DecidableEq Rest]
  frame : (D × Rest) ≃ P
  wires : WireEmbedding dataChart chart frame
attribute [instance] TensorLayout.finiteRest TensorLayout.decidableRest

abbrev OutputLayout (chart : P ≃ (W → Bool)) (n : ℕ) := TensorLayout chart (sumCoordinates n)

def measuredBit (chart : P ≃ (W → Bool)) (i : W) (b : Bool) : Matrix P P ℂ :=
  Matrix.diagonal (fun x=>if chart x i=b then 1 else 0)

theorem measuredBit_normalized (chart : P ≃ (W → Bool)) (i : W) :
    ∑ b : Fin 2,(measuredBit chart i (Refinement.CostedExecution.outcome b))ᴴ*
      measuredBit chart i (Refinement.CostedExecution.outcome b)=1 := by
  rw [Fin.sum_univ_two]
  change (measuredBit chart i false)ᴴ*measuredBit chart i false+
    (measuredBit chart i true)ᴴ*measuredBit chart i true=1
  ext x y
  by_cases h:x=y
  · subst y
    cases hb:chart x i <;>
      simp [measuredBit,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.diagonal,hb]
  · simp [measuredBit,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.diagonal,h,Ne.symm h]

variable {chart : P ≃ (W → Bool)} {n a : ℕ}
variable {D V : Type} [Fintype D] [DecidableEq D] {dataChart : D ≃ (V → Bool)}

def TensorLayout.kraus (F : TensorLayout chart dataChart) (r : F.Rest) :
    Matrix D P ℂ := fun i x=>if F.frame (i,r)=x then 1 else 0

theorem TensorLayout.kraus_normalized (F : TensorLayout chart dataChart) :
    ∑ r,(F.kraus r)ᴴ*F.kraus r=1 := by
  ext x y
  obtain ⟨⟨i,r⟩,rfl⟩:=F.frame.surjective x
  obtain ⟨⟨j,s⟩,rfl⟩:=F.frame.surjective y
  simp [TensorLayout.kraus,Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
    F.frame.injective.eq_iff,Prod.mk.injEq,Matrix.one_apply,ite_and,apply_ite]
  split_ifs <;> simp_all [eq_comm]

/-- Execution-order source syntax. Unit-cost work leaves are precisely actual
one/two-qubit gates; measurements have a separate explicit counter. -/
inductive SourceProgram (chart : P ≃ (W → Bool)) (a n : ℕ) where
  | step (i : SourceInstruction chart a n) (next : SourceProgram chart a n)
  | measure (i : W) (next : Bool → SourceProgram chart a n)
  | finish (success : Bool)

namespace SourceProgram

def work : SourceProgram chart a n → ℕ
  | .step i next => i.work+next.work
  | .measure _ next => max (next false).work (next true).work
  | .finish _ => 0

def measurements : SourceProgram chart a n → ℕ
  | .step _ next => next.measurements
  | .measure _ next => max (next false).measurements (next true).measurements+1
  | .finish _ => 0

def matrixCalls : SourceProgram chart a n → ℕ
  | .step i next => i.matrixCalls+next.matrixCalls
  | .measure _ next => max (next false).matrixCalls (next true).matrixCalls
  | .finish _ => 0

def vectorCalls : SourceProgram chart a n → ℕ
  | .step i next => i.vectorCalls+next.vectorCalls
  | .measure _ next => max (next false).vectorCalls (next true).vectorCalls
  | .finish _ => 0

end SourceProgram
end OptimalQLS.Reduction.GenericSolver.FreshCopies
