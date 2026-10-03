import OptimalQLS.KernelReflectionEncoding

noncomputable section
namespace OptimalQLS
open Matrix
variable {S D : Type*} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]

@[simp] theorem signalInjection_mulVec (s₀ : S) (x : D → ℂ) (s : S) (i : D) :
    (signalInjection s₀ *ᵥ x) (s,i) = if s = s₀ then x i else 0 := by
  simp [signalInjection, Matrix.mulVec, dotProduct, ite_and]

/-- Signal insertion is a literal Hilbert-space linear isometry. -/
def signalIsometry (s₀ : S) : EuclideanSpace ℂ D →ₗᵢ[ℂ] EuclideanSpace ℂ (S × D) where
  toFun x := WithLp.toLp 2 (signalInjection s₀ *ᵥ WithLp.ofLp x)
  map_add' x y := by ext ⟨s,i⟩; by_cases h : s = s₀ <;> simp [h]
  map_smul' c x := by ext ⟨s,i⟩; by_cases h : s = s₀ <;> simp [h]
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, WithLp.toLp_ofLp,
      PiLp.toLp_apply, signalInjection_mulVec]
    simp [apply_ite]

@[simp] theorem signalIsometry_apply (s₀ : S) (x : EuclideanSpace ℂ D) (s : S) (i : D) :
    signalIsometry s₀ x (s,i) = if s = s₀ then x i else 0 := signalInjection_mulVec s₀ _ s i

end OptimalQLS
