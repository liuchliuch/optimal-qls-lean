import OptimalQLS.Reduction.GenericSolver.FreshCopiesHeadSemantics

/-! Finite-coordinate semantics of the same physical head extraction and
partial traces. Successful-leaf guarantees follow actual Kraus branch vectors. -/
noncomputable section
open scoped Classical BigOperators
namespace OptimalQLS.Reduction.GenericSolver.FreshCopies
open Matrix LowerBounds Refinement.Repetition TransducerCompiler BinaryClock PolynomialTransform
open Refinement.CostedExecution
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

theorem indexedRight (n : ℕ) (v : Bits n ⊕ Bits n → ℂ) :
    (fun i=>indexedVector (doubledRegister n) v (extractRightEmbedding (doubledIndex n) i))=
      indexedVector (dataRegister n) (fun i=>v (.inr i)) := by
  ext i
  simp [indexedVector,extractRightEmbedding,doubledIndex]
  exact congrArg v ((doubledRegister n).index.symm_apply_apply _)

theorem indexedLeftMass (n : ℕ) (v : Bits n ⊕ Bits n → ℂ) :
    bornMass (fun i=>v (.inl i))=bornMass (indexedVector (doubledRegister n) v)-
      bornMass (fun i=>indexedVector (doubledRegister n) v (extractRightEmbedding (doubledIndex n) i)) := by
  rw [indexedRight,indexedVector_bornMass,indexedVector_bornMass]
  change (∑ i : Bits n,Complex.normSq (v (.inl i)))=
    (∑ i : Bits n ⊕ Bits n,Complex.normSq (v i))-(∑ i : Bits n,Complex.normSq (v (.inr i)))
  rw [Fintype.sum_sum_type]
  ring

variable {A B VA VB : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable {argumentsA : A ≃ (VA → Bool)} {argumentsB : B ≃ (VB → Bool)}

theorem traceFirst_density (R T O : Register) (next : Process argumentsA argumentsB O T)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (select : Bool → Bool)
    (x : Fin R.dimension → ℂ) (z : Fin T.dimension → ℂ) :
    (Process.trace (discardFirstLayout R T) next).lower.executeDensity UA Ub select (tensorVector x z)=
      bornMass x • next.lower.executeDensity UA Ub select z := by
  have hh:=traceFirst_runDensity R T O next UA Ub select (x ∘ R.index) (z ∘ T.index)
  have hx:=indexedVector_comp_index R x
  have hz:=indexedVector_comp_index T z
  have hm:=indexedVector_bornMass R (x ∘ R.index)
  rw [hx] at hm
  rw [←Process.lower_runDensity,indexedVector_product,hx,hz] at hh
  have hn:=Process.lower_runDensity UA Ub select next (z ∘ T.index)
  rw [hz] at hn
  rw [←hn,←hm] at hh
  exact hh

theorem headProcess_density (n : ℕ) (T : Register)
    (next : Process argumentsA argumentsB (dataRegister n) T)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (select : Bool → Bool)
    (x : Fin (doubledRegister n).dimension → ℂ) (z : Fin T.dimension → ℂ) :
    (headProcess n T next).lower.executeDensity UA Ub select (tensorVector x z)=
      (if select true then bornMass z • pureDensity (fun i=>x (extractRightEmbedding (doubledIndex n) i)) else 0)+
      (bornMass x-bornMass (fun i=>x (extractRightEmbedding (doubledIndex n) i))) •
        next.lower.executeDensity UA Ub select z := by
  have hh:=headProcess_runDensity n T next UA Ub select (x ∘ (doubledRegister n).index) (z ∘ T.index)
  have hx:=indexedVector_comp_index (doubledRegister n) x
  have hz:=indexedVector_comp_index T z
  have hm:=indexedVector_bornMass T (z ∘ T.index)
  rw [hz] at hm
  have ha:=indexedRight n (x ∘ (doubledRegister n).index)
  rw [hx] at ha
  have hl:=indexedLeftMass n (x ∘ (doubledRegister n).index)
  rw [hx] at hl
  rw [←Process.lower_runDensity,indexedVector_product,hx,hz] at hh
  have hn:=Process.lower_runDensity UA Ub select next (z ∘ T.index)
  rw [hz] at hn
  rw [←hn,←hm,←ha,hl] at hh
  exact hh

theorem traceFirst_returns (R T O : Register) (next : Process argumentsA argumentsB O T)
    (Pred : (Fin O.dimension → ℂ) → Prop)
    (hPred : ∀ v (c : ℂ),Pred v→Pred (c • v))
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (x : Fin R.dimension → ℂ) (z : Fin T.dimension → ℂ)
    (hnext : Returns Pred UA Ub next.lower z) :
    Returns Pred UA Ub (Process.trace (discardFirstLayout R T) next).lower (tensorVector x z) := by
  have hx:=indexedVector_comp_index R x
  have hz:=indexedVector_comp_index T z
  have hn:next.runReturns Pred UA Ub (z ∘ T.index) := by
    rw [←Process.lower_runReturns,hz]
    exact hnext
  have hh:=traceFirst_runReturns R T O next Pred hPred UA Ub (x ∘ R.index) (z ∘ T.index) hn
  rw [←Process.lower_runReturns,indexedVector_product,hx,hz] at hh
  exact hh

theorem headProcess_returns (n : ℕ) (T : Register)
    (next : Process argumentsA argumentsB (dataRegister n) T)
    (Pred : (Fin (dataRegister n).dimension → ℂ) → Prop)
    (hPred : ∀ v (c : ℂ),Pred v→Pred (c • v))
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (x : Fin (doubledRegister n).dimension → ℂ) (z : Fin T.dimension → ℂ)
    (haccept : Pred (fun i=>x (extractRightEmbedding (doubledIndex n) i)))
    (hnext : Returns Pred UA Ub next.lower z) :
    Returns Pred UA Ub (headProcess n T next).lower (tensorVector x z) := by
  have hx:=indexedVector_comp_index (doubledRegister n) x
  have hz:=indexedVector_comp_index T z
  have ha:=indexedRight n (x ∘ (doubledRegister n).index)
  rw [hx] at ha
  have hn:next.runReturns Pred UA Ub (z ∘ T.index) := by
    rw [←Process.lower_runReturns,hz]
    exact hnext
  have hh:=headProcess_runReturns n T next Pred hPred UA Ub
    (x ∘ (doubledRegister n).index) (z ∘ T.index) (ha ▸ haccept) hn
  rw [←Process.lower_runReturns,indexedVector_product,hx,hz] at hh
  exact hh

end OptimalQLS.Reduction.GenericSolver.FreshCopies
