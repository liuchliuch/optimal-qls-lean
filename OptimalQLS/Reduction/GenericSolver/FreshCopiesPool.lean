import OptimalQLS.Reduction.GenericSolver.FreshCopiesPhysicalRetry
import OptimalQLS.Reduction.GenericSolver.FreshCopiesProcessTensorExecution

/-! Literal all-zero fresh registers, with no copies of an unknown input state. -/
noncomputable section
open scoped Classical
namespace OptimalQLS.Reduction.GenericSolver.FreshCopies
open Matrix LowerBounds Refinement.Repetition TransducerCompiler BinaryClock
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

theorem basis_tensor {m r : ℕ} (i : Fin m) (j : Fin r) :
    tensorVector (basis i) (basis j)=basis (finProdFinEquiv (i,j)) := by
  ext k
  obtain ⟨⟨s,t⟩,rfl⟩:=finProdFinEquiv.surjective k
  simp only [tensorVector,Equiv.symm_apply_apply,basis,finProdFinEquiv.injective.eq_iff,Prod.mk.injEq]
  by_cases hs:s=i <;> by_cases ht:t=j <;> simp [hs,ht]

def poolBasis (R : Register) (n : ℕ) (zero : R.State) (out : Bits n) (k : ℕ) :
    Fin (poolRegister R n k).dimension → ℂ :=
  basis ((poolRegister R n k).index (poolPoint R n zero out k))

theorem poolBasis_zero (R : Register) (n : ℕ) (zero : R.State) (out : Bits n) :
    poolBasis R n zero out 0=basis ((dataRegister n).index out) := rfl

theorem poolBasis_succ (R : Register) (n : ℕ) (zero : R.State) (out : Bits n) (k : ℕ) :
    poolBasis R n zero out (k+1)=tensorVector (basis (R.index zero)) (poolBasis R n zero out k) := by
  change basis (finProdFinEquiv (R.index zero,(poolRegister R n k).index (poolPoint R n zero out k)))=_
  exact (basis_tensor _ _).symm

theorem poolBasis_bornMass (R : Register) (n : ℕ) (zero : R.State) (out : Bits n) (k : ℕ) :
    bornMass (poolBasis R n zero out k)=1 := basis_bornMass _

theorem poolPoint_zero_bits (R : Register) (n : ℕ) (zero : R.State)
    (hz : R.bits zero=fun _=>false) (k : ℕ) :
    (poolRegister R n k).bits (poolPoint R n zero (fun _=>false) k)=fun _=>false := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i
    cases i with
    | inl i => change R.bits zero i=false;rw [hz]
    | inr i => exact congrFun ih i

theorem poolRegister_dimension (R : Register) (n k : ℕ) :
    (poolRegister R n k).dimension=2^(k*R.qubits+n) := by
  rw [Register.dimension_eq,poolRegister_qubits]

end OptimalQLS.Reduction.GenericSolver.FreshCopies
