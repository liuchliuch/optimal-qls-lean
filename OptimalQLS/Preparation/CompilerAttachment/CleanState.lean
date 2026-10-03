import OptimalQLS.Preparation.CompilerAttachment.Frames

/-! # Exact norm and spectator-scratch behavior of the physical state embedding -/
noncomputable section
set_option synthInstance.maxSize 8192
open scoped Classical
namespace OptimalQLS.Preparation.CompilerAttachment
open Matrix TransducerCompiler PolynomialTransform

theorem cleanVector_apply (a n ℓ : ℕ) (v : Logical a n ℓ→ℂ)
    (x : Logical a n ℓ) (s : PhaseScratch) :
    (basisInsertion (clean a n ℓ)*ᵥv) (x,s)=
      if s=(false,false,false) then v x else 0 := by
  simp [basisInsertion,clean,Matrix.mulVec,dotProduct,Prod.mk.injEq,ite_and]

theorem cleanVector_norm (a n ℓ : ℕ) (v : Logical a n ℓ→ℂ) :
    ‖WithLp.toLp 2 (basisInsertion (clean a n ℓ)*ᵥv)‖=‖WithLp.toLp 2 v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  simp [cleanVector_apply,apply_ite]

theorem cleanVector_sub_norm (a n ℓ : ℕ) (v w : Logical a n ℓ→ℂ) :
    ‖WithLp.toLp 2 (basisInsertion (clean a n ℓ)*ᵥv-basisInsertion (clean a n ℓ)*ᵥw)‖=
      ‖WithLp.toLp 2 (v-w)‖ := by
  rw [← Matrix.mulVec_sub,cleanVector_norm]

end OptimalQLS.Preparation.CompilerAttachment
