import OptimalQLS.Reduction.GenericSolver.PhysicalExecution
import OptimalQLS.Reduction.GenericSolver.PhysicalFrames

/-! A fresh tensor factor: old-bit measurement and literal output partial
trace preserve its fixed basis state, without any reset or swap gates. -/
noncomputable section
open scoped Classical BigOperators
namespace OptimalQLS.Reduction.GenericSolver.Physical
open Matrix LowerBounds PolynomialTransform TransducerCompiler
open Refinement.CostedExecution FreshCopies
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
variable {P Q S W Z D V : Type} [Fintype P] [DecidableEq P]
  [Fintype Q] [DecidableEq Q] [Fintype S] [DecidableEq S]
  [Fintype D] [DecidableEq D]
  {chart : P ≃ (W → Bool)} {targetChart : Q ≃ (Z → Bool)} {dataChart : D ≃ (V → Bool)}

def inserted (e : P × S ≃ Q) (s : S) (v : P → ℂ) : Q → ℂ :=
  basisInsertion (fun p => e (p,s))*ᵥv

theorem inserted_at (e : P × S ≃ Q) (s t : S) (v : P → ℂ) (p : P) :
    inserted e s v (e (p,t))=if t=s then v p else 0 := by
  simp [inserted,basisInsertion,Matrix.mulVec,dotProduct,e.injective.eq_iff,Prod.mk.injEq,ite_and]

theorem inserted_intertwines (e : P × S ≃ Q) (s : S)
    (U : Matrix Q Q ℂ) (V : Matrix P P ℂ)
    (h : U*basisInsertion (fun p=>e (p,s))=basisInsertion (fun p=>e (p,s))*V)
    (v : P → ℂ) : U*ᵥinserted e s v=inserted e s (V*ᵥv) := by
  simpa only [inserted,Matrix.mulVec_mulVec] using congrArg (fun M=>M*ᵥv) h

def extendedLayout (e : P × S ≃ Q) (hw : WireEmbedding chart targetChart e)
    (F : TensorLayout chart dataChart) : TensorLayout targetChart dataChart where
  Rest := F.Rest × S
  frame := tensorFrame F.frame e
  wires := F.wires.comp hw

theorem measuredBit_inserted (e : P × S ≃ Q) (hw : WireEmbedding chart targetChart e)
    (s : S) (i : W) (b : Bool) (v : P → ℂ) :
    measuredBit targetChart (hw.wire i) b*ᵥinserted e s v=
      inserted e s (measuredBit chart i b*ᵥv) := by
  ext q
  obtain ⟨⟨p,t⟩,rfl⟩ := e.surjective q
  simp [measuredBit,Matrix.mulVec,dotProduct,Matrix.diagonal,inserted_at,hw.read]
  split_ifs <;> rfl

theorem extendedLayout_kraus (e : P × S ≃ Q) (hw : WireEmbedding chart targetChart e)
    (F : TensorLayout chart dataChart) (s t : S) (r : F.Rest) :
    (extendedLayout e hw F).kraus (r,t)*basisInsertion (fun p=>e (p,s))=
      if t=s then F.kraus r else 0 := by
  ext d p
  by_cases ht : t=s <;>
    simp [extendedLayout,TensorLayout.kraus,tensorFrame,Matrix.mul_apply,basisInsertion,
      e.injective.eq_iff,Prod.mk.injEq,ht,ite_and]

theorem extendedLayout_kraus_apply (e : P × S ≃ Q) (hw : WireEmbedding chart targetChart e)
    (F : TensorLayout chart dataChart) (s t : S) (r : F.Rest) (v : P → ℂ) :
    (extendedLayout e hw F).kraus (r,t)*ᵥinserted e s v=
      if t=s then F.kraus r*ᵥv else 0 := by
  rw [inserted,Matrix.mulVec_mulVec,extendedLayout_kraus]
  split_ifs <;> simp

theorem extendedLayout_density (e : P × S ≃ Q) (hw : WireEmbedding chart targetChart e)
    (F : TensorLayout chart dataChart) (s : S) (v : P → ℂ) (flag : Bool) :
    (∑ r : (extendedLayout e hw F).Rest,
      if flag then pureDensity (finiteVector ((extendedLayout e hw F).kraus r*ᵥinserted e s v)) else 0)=
    ∑ r : F.Rest, if flag then pureDensity (finiteVector (F.kraus r*ᵥv)) else 0 := by
  change (∑ r : F.Rest × S, _) = _
  rw [Fintype.sum_prod_type]
  simp only [extendedLayout_kraus_apply]
  cases flag
  · simp
  · simp only [ite_true]
    apply Finset.sum_congr rfl
    intro r _
    calc
      _ = ∑ t : S, if t=s then pureDensity (finiteVector (F.kraus r*ᵥv)) else 0 := by
        apply Finset.sum_congr rfl
        intro t _
        split_ifs <;> simp [finiteVector,pureDensity,ketBra]
      _ = _ := by simp

theorem extendedLayout_returns (e : P × S ≃ Q) (hw : WireEmbedding chart targetChart e)
    (F : TensorLayout chart dataChart) (s : S) (v : P → ℂ) (flag : Bool)
    (Pred : (Fin (Fintype.card D) → ℂ) → Prop) (hzero : Pred 0) :
    (∀ r : (extendedLayout e hw F).Rest, flag=true →
      Pred (finiteVector ((extendedLayout e hw F).kraus r*ᵥinserted e s v))) ↔
    (∀ r : F.Rest, flag=true → Pred (finiteVector (F.kraus r*ᵥv))) := by
  constructor
  · intro h r hf
    simpa only [extendedLayout_kraus_apply,ite_true] using h (r,s) hf
  · intro h r hf
    rcases r with ⟨r,t⟩
    rw [extendedLayout_kraus_apply]
    split_ifs
    · exact h r hf
    · exact hzero

end OptimalQLS.Reduction.GenericSolver.Physical
