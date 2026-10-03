import OptimalQLS.TwoReflectionNorms

noncomputable section
namespace OptimalQLS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (K : Submodule ℂ E) [K.HasOrthogonalProjection]

/-- The actual unitary used for overlap amplification. -/
def kernelMixingUnitary (e : E) (he : ‖e‖ = 1) : unitary (E →L[ℂ] E) :=
  twoReflectionUnitary K.starProjection
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr K.starProjection_isSymmetric)
    K.isIdempotentElem_starProjection e he

/-- Orthogonal decomposition quantities, all derived from the actual projector. -/
theorem kernelProjection_plane_data (e : E) (he : ‖e‖ = 1) :
    let p := K.starProjection e
    let w := e-p
    inner ℂ p w = 0 ∧ ‖p‖^2+‖w‖^2=1 ∧
    inner ℂ e p = (‖p‖^2 : ℝ) ∧ inner ℂ e w = ((1-‖p‖^2 : ℝ) : ℂ) := by
  dsimp only
  have hwp : inner ℂ (e-K.starProjection e) (K.starProjection e) = 0 :=
    K.starProjection_inner_eq_zero e _ (K.starProjection_apply_mem e)
  have hpw : inner ℂ (K.starProjection e) (e-K.starProjection e) = 0 := inner_eq_zero_symm.mp hwp
  have heq : e = K.starProjection e + (e-K.starProjection e) := by abel
  have hn : ‖K.starProjection e‖^2+‖e-K.starProjection e‖^2=1 := by
    have h := norm_add_sq (𝕜 := ℂ) (K.starProjection e) (e-K.starProjection e)
    rw [← heq, he, hpw, RCLike.zero_re] at h
    nlinarith
  refine ⟨hpw, hn, ?_, ?_⟩
  · conv_lhs => arg 2; rw [heq]
    rw [inner_add_left, hwp, add_zero, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  · conv_lhs => arg 2; rw [heq]
    rw [inner_add_left, hpw, zero_add, inner_self_eq_norm_sq_to_K]
    rw [← RCLike.ofReal_pow]
    exact congrArg (fun a : ℝ => (RCLike.ofReal a : ℂ)) (show ‖e-K.starProjection e‖^2 = 1-‖K.starProjection e‖^2 by linarith)

theorem kernelMixingUnitary_plane (e : E) (he : ‖e‖ = 1) :
    let p := K.starProjection e
    let w := e-p
    let x := ‖p‖^2
    (kernelMixingUnitary K e he : E →L[ℂ] E) p = (1-2*x) • p - (2*x) • w ∧
    (kernelMixingUnitary K e he : E →L[ℂ] E) w = (2*(1-x)) • p + (1-2*x) • w := by
  dsimp only
  have h := kernelProjection_plane_data K e he
  apply twoReflection_plane K.starProjection _ _ e he _ _ (by abel)
  · exact Submodule.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem e)
  · rw [map_sub, Submodule.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem e), sub_self]
  · exact h.2.2.1
  · exact h.2.2.2

/-- A normalized kernel vector extracts the literal real coefficient. -/
theorem normalized_projection_overlap (p w : E) (hp : p ≠ 0)
    (ho : inner ℂ p w = 0) (a b : ℝ) :
    inner ℂ (NormedSpace.normalize p) (a • p + b • w) = ((a*‖p‖ : ℝ) : ℂ) := by
  have hpn : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
  simp only [NormedSpace.normalize, inner_smul_left_eq_smul, inner_add_right,
    inner_smul_right_eq_smul, ho, smul_zero, add_zero, inner_self_eq_norm_sq_to_K]
  simp only [RCLike.real_smul_eq_coe_mul, RCLike.ofReal_mul, RCLike.ofReal_pow,
    RCLike.ofReal_inv, RCLike.ofReal_div, RCLike.ofReal_one]
  have hc : (‖p‖ : ℂ) ≠ 0 := by exact_mod_cast hpn
  field_simp
  exact (Complex.ofReal_mul a ‖p‖).symm

end OptimalQLS
