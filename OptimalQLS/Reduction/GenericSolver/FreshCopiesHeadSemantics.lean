import OptimalQLS.Reduction.GenericSolver.FreshCopiesHeadProcess
import OptimalQLS.Reduction.GenericSolver.FreshCopiesProcessTensorExecution

/-! Exact density and successful-leaf semantics of the literal physical head
measurement and tensor-factor traces. -/
noncomputable section
open scoped Classical BigOperators
namespace OptimalQLS.Reduction.GenericSolver.FreshCopies
open Matrix LowerBounds Refinement.Repetition TransducerCompiler BinaryClock PolynomialTransform
open Refinement.CostedExecution
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

variable {P W D V : Type} [Fintype P] [DecidableEq P] [Fintype D] [DecidableEq D]
  {chart : P ≃ (W → Bool)} {dataChart : D ≃ (V → Bool)}

theorem TensorLayout.kraus_mulVec (F : TensorLayout chart dataChart) (r : F.Rest) (v : P → ℂ) :
    F.kraus r*ᵥv=fun i=>v (F.frame (i,r)) := by
  ext i
  simp [TensorLayout.kraus,Matrix.mulVec,dotProduct]

theorem indexedVector_bornMass (R : Register) (v : R.State → ℂ) :
    bornMass (indexedVector R v)=bornMass v := by
  simp only [bornMass,indexedVector,Function.comp_def]
  exact R.index.symm.sum_comp (fun i=>Complex.normSq (v i))

def dataHead {n : ℕ} : (Bits n ⊕ Bits n) → Bool
  | .inl _ => false
  | .inr _ => true

theorem dataHead_read (n : ℕ) (x : Bits n ⊕ Bits n) :
    (doubledRegister n).bits x (0 : Fin (n+1))=dataHead x := by cases x <;> rfl

def headVector (n : ℕ) (T : Register) (b : Bool) (v : Bits n ⊕ Bits n → ℂ)
    (z : T.State → ℂ) : ((doubledRegister n).product T).State → ℂ :=
  measuredBit ((doubledRegister n).product T).bits (.inl (0 : Fin (n+1))) b *ᵥ
    (fun p=>v p.1*z p.2)

theorem headVector_apply (n : ℕ) (T : Register) (b : Bool)
    (v : Bits n ⊕ Bits n → ℂ) (z : T.State → ℂ) (x : Bits n ⊕ Bits n) (t : T.State) :
    headVector n T b v z (x,t)=if dataHead x=b then v x*z t else 0 := by
  simp only [headVector,measuredBit,Matrix.mulVec_diagonal]
  change (if (doubledRegister n).bits x (0 : Fin (n+1))=b then (1:ℂ) else 0)*(v x*z t)=_
  rw [dataHead_read]
  split_ifs <;> simp

theorem right_head_slice (n : ℕ) (T : Register) (v : Bits n ⊕ Bits n → ℂ)
    (z : T.State → ℂ) (r : Bool × T.State) :
    (rightDataLayout n T).kraus r*ᵥheadVector n T true v z=
      (if r.1 then z r.2 else (0:ℂ)) • (fun x=>v (.inr x)) := by
  rw [TensorLayout.kraus_mulVec]
  ext x
  rcases r with ⟨b,t⟩
  cases b <;> simp [rightDataLayout,headVector_apply,dataHead,mul_comm]

theorem left_head_slice (n : ℕ) (T : Register) (v : Bits n ⊕ Bits n → ℂ)
    (z : T.State → ℂ) (r : Bits n ⊕ Bits n) :
    (discardFirstLayout (doubledRegister n) T).kraus r*ᵥheadVector n T false v z=
      (if dataHead r=false then v r else (0:ℂ)) • z := by
  rw [TensorLayout.kraus_mulVec]
  ext x
  change headVector n T false v z (r,x)=(if dataHead r=false then v r else 0)*z x
  rw [headVector_apply]
  split_ifs <;> simp

variable {A B VA VB : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable {argumentsA : A ≃ (VA → Bool)} {argumentsB : B ≃ (VB → Bool)}

theorem traceFirst_runDensity (R T O : Register) (next : Process argumentsA argumentsB O T)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (select : Bool → Bool)
    (v : R.State → ℂ) (z : T.State → ℂ) :
    (Process.trace (discardFirstLayout R T) next).runDensity UA Ub select (fun p=>v p.1*z p.2)=
      bornMass v • next.runDensity UA Ub select z := by
  have he (r : R.State) : (discardFirstLayout R T).kraus r*ᵥ(fun p=>v p.1*z p.2)=v r • z := by
    rw [TensorLayout.kraus_mulVec]
    rfl
  simp only [Process.runDensity,he,Process.runDensity_smul,←Finset.sum_smul]
  rfl

theorem headProcess_runDensity (n : ℕ) (T : Register)
    (next : Process argumentsA argumentsB (dataRegister n) T)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (select : Bool → Bool)
    (v : Bits n ⊕ Bits n → ℂ) (z : T.State → ℂ) :
    (headProcess n T next).runDensity UA Ub select (fun p=>v p.1*z p.2)=
      (if select true then bornMass z • pureDensity (indexedVector (dataRegister n) (fun x=>v (.inr x))) else 0)+
      bornMass (fun x=>v (.inl x)) • next.runDensity UA Ub select z := by
  have ha : (Process.trace (rightDataLayout n T) (Process.output true :
      Process argumentsA argumentsB (dataRegister n) (dataRegister n))).runDensity UA Ub select
      (headVector n T true v z)=
      (if select true then bornMass z • pureDensity (indexedVector (dataRegister n) (fun x=>v (.inr x))) else 0) := by
    simp only [Process.runDensity,right_head_slice,indexedVector_smul,pureDensity_complex_smul]
    cases hs:select true <;> simp only [hs,Bool.false_eq_true,ite_false,ite_true,Finset.sum_const_zero]
    change (∑ r : Bool × T.State, pureDensity (indexedVector (dataRegister n)
      ((if r.1 then z r.2 else (0:ℂ)) • (fun x=>v (.inr x)))))=_
    have hsml (r : Bool × T.State) :
        pureDensity (indexedVector (dataRegister n) ((if r.1 then z r.2 else (0:ℂ)) • (fun x=>v (.inr x))))=
        Complex.normSq (if r.1 then z r.2 else (0:ℂ)) • pureDensity (indexedVector (dataRegister n) (fun x=>v (.inr x))) := by
      rw [indexedVector_smul,pureDensity_complex_smul]
      rfl
    simp only [hsml]
    rw [←Finset.sum_smul]
    congr 1
    simp [bornMass,Fintype.sum_prod_type]
  have hb : (Process.trace (discardFirstLayout (doubledRegister n) T) next).runDensity UA Ub select
      (headVector n T false v z)=bornMass (fun x=>v (.inl x)) • next.runDensity UA Ub select z := by
    simp only [Process.runDensity,left_head_slice,Process.runDensity_smul,←Finset.sum_smul]
    congr 1
    change (∑ x : Bits n ⊕ Bits n, Complex.normSq (if dataHead x=false then v x else 0))=_
    rw [Fintype.sum_sum_type]
    simp [bornMass,dataHead]
  change _= _
  simp only [headProcess,Process.runDensity,Fin.sum_univ_two,outcome]
  change (Process.trace (discardFirstLayout (doubledRegister n) T) next).runDensity UA Ub select
      (headVector n T false v z)+
    (Process.trace (rightDataLayout n T) (Process.output true)).runDensity UA Ub select
      (headVector n T true v z)=_
  rw [ha,hb,add_comm]


theorem traceFirst_runReturns (R T O : Register) (next : Process argumentsA argumentsB O T)
    (Pred : (Fin O.dimension → ℂ) → Prop)
    (hPred : ∀ v (c : ℂ),Pred v→Pred (c • v))
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (v : R.State → ℂ) (z : T.State → ℂ)
    (hnext : next.runReturns Pred UA Ub z) :
    (Process.trace (discardFirstLayout R T) next).runReturns Pred UA Ub (fun p=>v p.1*z p.2) := by
  intro r
  have he : (discardFirstLayout R T).kraus r*ᵥ(fun p=>v p.1*z p.2)=v r • z := by
    rw [TensorLayout.kraus_mulVec]
    rfl
  rw [he]
  exact Process.runReturns_smul Pred hPred UA Ub next z hnext (v r)

theorem headProcess_runReturns (n : ℕ) (T : Register)
    (next : Process argumentsA argumentsB (dataRegister n) T)
    (Pred : (Fin (dataRegister n).dimension → ℂ) → Prop)
    (hPred : ∀ v (c : ℂ),Pred v→Pred (c • v))
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (v : Bits n ⊕ Bits n → ℂ) (z : T.State → ℂ)
    (haccept : Pred (indexedVector (dataRegister n) (fun i=>v (.inr i))))
    (hnext : next.runReturns Pred UA Ub z) :
    (headProcess n T next).runReturns Pred UA Ub (fun p=>v p.1*z p.2) := by
  change ∀ b : Fin 2, _
  intro b
  fin_cases b
  · change ∀ r, next.runReturns Pred UA Ub
      ((discardFirstLayout (doubledRegister n) T).kraus r*ᵥheadVector n T false v z)
    intro r
    rw [left_head_slice]
    exact Process.runReturns_smul Pred hPred UA Ub next z hnext _
  · change ∀ r, true=true → Pred (indexedVector (dataRegister n)
      ((rightDataLayout n T).kraus r*ᵥheadVector n T true v z))
    intro r _
    rw [right_head_slice,indexedVector_smul]
    exact hPred _ _ haccept

end OptimalQLS.Reduction.GenericSolver.FreshCopies
