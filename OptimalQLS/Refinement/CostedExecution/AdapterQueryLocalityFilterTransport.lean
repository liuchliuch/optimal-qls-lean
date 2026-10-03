import OptimalQLS.Refinement.CostedExecution.AdapterQueryLocalityCore
import OptimalQLS.Refinement.CostedExecution.QueryLocalityFilter
noncomputable section
namespace OptimalQLS.Refinement.CostedExecution
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
open PhysicalProgram PhysicalMeasurement Reduction PhysicalAdapter
open scoped Classical
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false

theorem WireEmbedding.agree_at {S W Q P R : Type}
    {q : Q → S → Bool} {c : P → W → Bool} {e : Q × R ≃ P}
    (H : WireEmbedding q c e) (x y : Q) (r : R) (j : W)
    (h : ∀ i, H.wire i=j → q x i=q y i) : c (e (x,r)) j=c (e (y,r)) j := by
  by_cases hj : ∃ i,H.wire i=j
  · obtain ⟨i,rfl⟩ := hj
    rw [H.read,H.read]
    exact h i rfl
  · exact H.outside x y r j (by simpa using hj)

theorem adapterOriginalMatrix_raw_formula (a n ℓ : ℕ) (f : PhysicalProgram.Flag)
    (v : Bool × (Bits a × Bits n)) (r : (adapterOriginalMatrixFrame a n ℓ f).Rest) :
    (adapterOriginalMatrixFrame a n ℓ f).wiring (v,r) =
      let t := (Fintype.equivFin (PhysicalAdapter.matrixFrame a n ℓ f).Rest).symm r.2
      ((matrixFrameRaw a (n+1) ℓ f).wiring
        ((r.1.2 ⟨.inl 0,by decide⟩,
          (v.2.1,Fin.cons (r.1.2 ⟨.inl 1,by decide⟩) v.2.2)),t),
        (r.1.1,v.1,r.1.2 ⟨.inr 1,by decide⟩)) := by
  rw [adapterOriginalMatrixFrame_apply,adapterMatrixFrame_apply]
  simp only [Equiv.funSplitAt_symm_apply,smallTarget,Sum.inl_ne_inr,↓reduceDIte,
    Fin.reduceEq,Sum.inr.injEq]

end OptimalQLS.Refinement.CostedExecution
