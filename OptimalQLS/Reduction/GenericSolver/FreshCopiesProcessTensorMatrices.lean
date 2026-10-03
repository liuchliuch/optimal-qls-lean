import OptimalQLS.Reduction.GenericSolver.FreshCopiesProcess

/-! Exact finite-coordinate actions of physical spectator tensoring. -/
noncomputable section
open scoped Classical BigOperators Kronecker
namespace OptimalQLS.Reduction.GenericSolver.FreshCopies
open Matrix TransducerCompiler PolynomialTransform
open Refinement.CostedExecution Refinement.PhysicalMeasurement Refinement.Repetition
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

/-- The register product uses exactly the finite Kronecker coordinates. -/
theorem indexedMatrix_tensor (R Q T : Register) (M : Matrix Q.State R.State ℂ) :
    indexedMatrix (R.product T) (Q.product T) (M ⊗ₖ (1 : Matrix T.State T.State ℂ)) =
      tensorRect T.dimension (indexedMatrix R Q M) := by
  ext i j
  simp [indexedMatrix,tensorRect,Register.product,Matrix.kronecker_apply,
    Matrix.one_apply,T.index.symm.injective.eq_iff]

theorem indexedMatrix_place (R T : Register) (U : Matrix.unitaryGroup R.State ℂ) :
    (rewireUnitary (R.product T).index (GateSynthesis.placeHom (Equiv.refl _) U)).val =
      tensorRect T.dimension (rewireUnitary R.index U).val := by
  have hp : (GateSynthesis.placeHom (Equiv.refl (R.State × T.State)) U).val =
      U.val ⊗ₖ (1 : Matrix T.State T.State ℂ) := by
    ext ⟨x,s⟩ ⟨y,t⟩
    have h := placeHom_entry (Equiv.refl (R.State × T.State)) U x y s t
    simpa [Matrix.kronecker_apply,Matrix.one_apply] using h
  change indexedMatrix (R.product T) (R.product T) _ =
    tensorRect T.dimension (indexedMatrix R R _)
  rw [hp,indexedMatrix_tensor]

theorem indexedPort_tensor {A : Type} [Fintype A] [DecidableEq A]
    (R T : Register) (p : QueryPort A R.State) (U : Matrix.unitaryGroup A ℂ) :
    ((reindexPort (R.product T).index
      ((scratchPort (Equiv.refl (R.State × T.State))).comp p)).apply U).val =
      tensorRect T.dimension ((reindexPort R.index p).apply U).val := by
  rw [reindexPort_apply,reindexPort_apply,QueryPort.comp_apply,scratchPort_apply]
  exact indexedMatrix_place R T (p.apply U)

theorem indexedMeasuredBit_tensor (R T : Register) (i : R.Wire) (b : Bool) :
    indexedMatrix (R.product T) (R.product T)
      (measuredBit (R.product T).bits (.inl i) b) =
      tensorRect T.dimension (indexedMatrix R R (measuredBit R.bits i b)) := by
  have hm : measuredBit (R.product T).bits (.inl i) b =
      measuredBit R.bits i b ⊗ₖ (1 : Matrix T.State T.State ℂ) := by
    ext ⟨x,s⟩ ⟨y,t⟩
    by_cases hxy : x=y <;> by_cases hst : s=t <;>
      simp [measuredBit,Matrix.diagonal,Register.product,productBits,
        Matrix.kronecker_apply,Matrix.one_apply,hxy,hst,Prod.mk.injEq]
  rw [hm,indexedMatrix_tensor]

theorem TensorLayout.indexedKraus_product {R Q : Register}
    (F : TensorLayout R.bits Q.bits) (T : Register)
    (i : Fin (Fintype.card F.Rest)) :
    (F.product T).indexedKraus i = tensorRect T.dimension (F.indexedKraus i) := by
  have hk (r : F.Rest) : (F.product T).kraus r =
      F.kraus r ⊗ₖ (1 : Matrix T.State T.State ℂ) := by
    ext ⟨x,s⟩ ⟨y,t⟩
    by_cases hxy : F.frame (x,r)=y <;> by_cases hst : s=t <;>
      simp [TensorLayout.kraus,TensorLayout.product,Matrix.kronecker_apply,
        Matrix.one_apply,hxy,hst,Prod.mk.injEq] <;>
      (intro h; cases h; contradiction)
  unfold TensorLayout.indexedKraus
  rw [hk,indexedMatrix_tensor]
  rfl

end OptimalQLS.Reduction.GenericSolver.FreshCopies
