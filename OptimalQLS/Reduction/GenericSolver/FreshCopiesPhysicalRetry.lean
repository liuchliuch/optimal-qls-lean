import OptimalQLS.Reduction.GenericSolver.FreshCopiesHeadProcess
import OptimalQLS.Reduction.GenericSolver.FreshCopiesProcessPaths
import OptimalQLS.Reduction.GenericSolver.FreshCopiesProcessTensor

/-! The actual physical three-copy reduction. All registers are initialized
once; failed used factors are traced out without reset or data-moving gates. -/
noncomputable section
open scoped Classical
namespace OptimalQLS.Reduction.GenericSolver.FreshCopies
open Matrix TransducerCompiler BinaryClock PolynomialTransform LowerBounds
open Refinement.CostedExecution
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

def poolRegister (R : Register) (n : ℕ) : ℕ → Register
  | 0 => dataRegister n
  | k+1 => R.product (poolRegister R n k)

def poolPoint (R : Register) (n : ℕ) (zero : R.State) (out : Bits n) :
    (k : ℕ) → (poolRegister R n k).State
  | 0 => out
  | k+1 => (zero,poolPoint R n zero out k)

theorem poolRegister_qubits (R : Register) (n k : ℕ) :
    (poolRegister R n k).qubits=k*R.qubits+n := by
  induction k with
  | zero => simp [poolRegister,dataRegister,Register.ofChart,Register.qubits]
  | succ k ih => rw [poolRegister,Register.product_qubits,ih,Nat.succ_mul];omega

variable {A B VA VB : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable {argumentsA : A ≃ (VA → Bool)} {argumentsB : B ≃ (VB → Bool)}

namespace Process

theorem output_qubits_le {O R : Register} (p : Process argumentsA argumentsB O R) :
    O.qubits≤R.qubits := by
  induction p with
  | unitary U h next ih => exact ih
  | matrix p adj L next ih => exact ih
  | vector p adj L next ih => exact ih
  | measure i next ih => exact ih false
  | trace F next ih => exact ih.trans F.output_qubits_le
  | output flag => exact le_rfl

end Process

def freshProcess (n : ℕ) (R : Register) (p : Process argumentsA argumentsB (doubledRegister n) R) :
    (k : ℕ) → Process argumentsA argumentsB (dataRegister n) (poolRegister R n k)
  | 0 => .output false
  | k+1 => (p.tensor (poolRegister R n k)).bindOutput
      (fun flag=>if flag then headProcess n (poolRegister R n k) (freshProcess n R p k)
        else .trace (discardFirstLayout (doubledRegister n) (poolRegister R n k)) (freshProcess n R p k))

theorem freshProcess_resources (n : ℕ) (R : Register)
    (p : Process argumentsA argumentsB (doubledRegister n) R) (k : ℕ) :
    (freshProcess n R p k).work≤k*p.work ∧
    (freshProcess n R p k).measurements≤k*(p.measurements+1) ∧
    (freshProcess n R p k).matrixCalls≤k*p.matrixCalls ∧
    (freshProcess n R p k).vectorCalls≤k*p.vectorCalls := by
  induction k with
  | zero => simp [freshProcess,Process.work,Process.measurements,Process.matrixCalls,Process.vectorCalls]
  | succ k ih =>
    let t:=poolRegister R n k
    let next:=freshProcess n R p k
    let cont:=fun flag:Bool=>if flag then headProcess n t next
      else Process.trace (discardFirstLayout (doubledRegister n) t) next
    have hw:∀b,(cont b).work≤next.work := by
      intro b;cases b
      · exact le_rfl
      · exact (headProcess_resources n t next).1.le
    have hm:∀b,(cont b).measurements≤next.measurements+1 := by
      intro b;cases b
      · change next.measurements≤next.measurements+1;omega
      · exact (headProcess_resources n t next).2.1.le
    have hA:∀b,(cont b).matrixCalls≤next.matrixCalls := by
      intro b;cases b
      · exact le_rfl
      · exact (headProcess_resources n t next).2.2.1.le
    have hB:∀b,(cont b).vectorCalls≤next.vectorCalls := by
      intro b;cases b
      · exact le_rfl
      · exact (headProcess_resources n t next).2.2.2.le
    have cw:=Process.bindOutput_work (p.tensor t) cont next.work hw
    have cm:=Process.bindOutput_measurements (p.tensor t) cont (next.measurements+1) hm
    have cA:=Process.bindOutput_matrixCalls (p.tensor t) cont next.matrixCalls hA
    have cB:=Process.bindOutput_vectorCalls (p.tensor t) cont next.vectorCalls hB
    rw [(p.tensor_resources t).1] at cw
    rw [(p.tensor_resources t).2.1] at cm
    rw [(p.tensor_resources t).2.2.1] at cA
    rw [(p.tensor_resources t).2.2.2] at cB
    change (freshProcess n R p (k+1)).work≤p.work+(freshProcess n R p k).work at cw
    change (freshProcess n R p (k+1)).measurements≤p.measurements+((freshProcess n R p k).measurements+1) at cm
    change (freshProcess n R p (k+1)).matrixCalls≤p.matrixCalls+(freshProcess n R p k).matrixCalls at cA
    change (freshProcess n R p (k+1)).vectorCalls≤p.vectorCalls+(freshProcess n R p k).vectorCalls at cB
    refine ⟨?_,?_,?_,?_⟩ <;> nlinarith only [cw,cm,cA,cB,ih.1,ih.2.1,ih.2.2.1,ih.2.2.2]

theorem freshProcess_query_depths (n : ℕ) (R : Register)
    (p : Process argumentsA argumentsB (doubledRegister n) R) (k : ℕ) :
    Refinement.Repetition.matrixDepth (freshProcess n R p k).lower≤k*p.matrixCalls ∧
    (freshProcess n R p k).lower.vectorDepth≤k*p.vectorCalls := by
  rw [Process.lower_matrixCalls,Process.lower_vectorCalls]
  exact ⟨(freshProcess_resources n R p k).2.2.1,(freshProcess_resources n R p k).2.2.2⟩

/-- At most four copies' worth of source wires, including the output fallback. -/
theorem fresh_three_qubits (n : ℕ) (R : Register)
    (p : Process argumentsA argumentsB (doubledRegister n) R) :
    (poolRegister R n 3).qubits≤4*R.qubits := by
  have h:=p.output_qubits_le
  have hn:(doubledRegister n).qubits=n+1 := by
    simp [doubledRegister,Register.ofChart,Register.qubits]
  rw [hn] at h
  rw [poolRegister_qubits]
  omega

theorem fresh_three_registerBound (n : ℕ) (R : Register)
    (p : Process argumentsA argumentsB (doubledRegister n) R) :
    Refinement.Repetition.RegisterBound (2^(4*R.qubits)) (freshProcess n R p 3).lower := by
  apply Process.lower_registerBound_le
  rw [(poolRegister R n 3).dimension_eq]
  exact pow_le_pow_right' (by decide : (1:ℕ)≤2) (fresh_three_qubits n R p)

end OptimalQLS.Reduction.GenericSolver.FreshCopies
