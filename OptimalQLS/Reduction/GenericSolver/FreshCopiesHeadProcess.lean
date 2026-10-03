import OptimalQLS.Reduction.GenericSolver.FreshCopiesProcessBind

/-! A literal head-qubit measurement and selected output-factor trace. The
failed factor is discarded, exposing the next already initialized register. -/
noncomputable section
open scoped Classical
namespace OptimalQLS.Reduction.GenericSolver.FreshCopies
open Matrix TransducerCompiler BinaryClock PolynomialTransform
open Refinement.CostedExecution
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

def dataRegister (n : ℕ) : Register := Register.ofChart (Equiv.refl (Bits n))
def doubledRegister (n : ℕ) : Register := Register.ofChart (sumCoordinates n)

def doubledIndex (n : ℕ) :
    (Fin (dataRegister n).dimension ⊕ Fin (dataRegister n).dimension) ≃ Fin (doubledRegister n).dimension :=
  (Equiv.sumCongr (dataRegister n).index.symm (dataRegister n).index.symm).trans
    (doubledRegister n).index

def discardFirstLayout (R T : Register) : TensorLayout (R.product T).bits T.bits where
  Rest := R.State
  frame := Equiv.prodComm _ _
  wires := {
    wire := Function.Embedding.inr
    read := by intros; rfl
    outside := by
      intro x y r j hj
      cases j with
      | inl j => rfl
      | inr j => exact False.elim (hj j rfl) }

def discardSecondLayout (R T : Register) : TensorLayout (R.product T).bits R.bits where
  Rest := T.State
  frame := Equiv.refl _
  wires := Register.firstEmbedding R T

/-- The output's physical wires are the successors of the source data head. -/
def rightDataLayout (n : ℕ) (T : Register) :
    TensorLayout ((doubledRegister n).product T).bits (dataRegister n).bits where
  Rest := Bool × T.State
  frame := {
    toFun p := (if p.2.1 then Sum.inr p.1 else Sum.inl p.1,p.2.2)
    invFun p := match p.1 with
      | .inl x => (x,(false,p.2))
      | .inr x => (x,(true,p.2))
    left_inv p := by rcases p with ⟨x,b,t⟩;cases b <;> rfl
    right_inv p := by rcases p with ⟨x,t⟩;cases x <;> rfl }
  wires := {
    wire := ⟨fun i=>.inl i.succ,by intro i j he;exact Fin.succ_injective _ (Sum.inl.inj he)⟩
    read := by
      intro x r i
      rcases r with ⟨b,t⟩
      cases b <;> rfl
    outside := by
      intro x y r j hj
      cases j with
      | inl j =>
        revert hj
        refine Fin.cases ?_ (fun k=>?_) j
        · intro hj;rcases r with ⟨b,t⟩;cases b <;> rfl
        · intro hj;exact False.elim (hj k rfl)
      | inr j => rfl }

variable {A B VA VB : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable {argumentsA : A ≃ (VA → Bool)} {argumentsB : B ≃ (VB → Bool)}

/-- The success bit is a literal one-qubit measurement; neither branch moves
or resets the output data. All unused factors are ordinary partial traces. -/
def headProcess (n : ℕ) (T : Register)
    (next : Process argumentsA argumentsB (dataRegister n) T) :
    Process argumentsA argumentsB (dataRegister n) ((doubledRegister n).product T) :=
  .measure (.inl (0 : Fin (n+1))) (fun b=>if b then .trace (rightDataLayout n T) (.output true)
    else .trace (discardFirstLayout (doubledRegister n) T) next)

theorem headProcess_resources (n : ℕ) (T : Register)
    (next : Process argumentsA argumentsB (dataRegister n) T) :
    (headProcess n T next).work=next.work ∧
    (headProcess n T next).measurements=next.measurements+1 ∧
    (headProcess n T next).matrixCalls=next.matrixCalls ∧
    (headProcess n T next).vectorCalls=next.vectorCalls := by
  simp [headProcess,Process.work,Process.measurements,Process.matrixCalls,Process.vectorCalls]

end OptimalQLS.Reduction.GenericSolver.FreshCopies
