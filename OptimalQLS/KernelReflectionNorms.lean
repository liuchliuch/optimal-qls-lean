import OptimalQLS.KernelReflection
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

noncomputable section
namespace OptimalQLS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Orthogonality of the two terms in the catalyst follows from the
signal compression and the genuine projection orthogonality. -/
theorem kernel_catalyst_orthogonal (Q V : E →L[ℂ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hV : V.toLinearMap.IsSymmetric)
    {α : ℝ} (ξ p z : E) (hp : Q p = p)
    (hVz : Q (V z) = α⁻¹ • (ξ - p))
    (horth : inner ℂ p (ξ - p) = 0) :
    inner ℂ p (V z) = 0 ∧ inner ℂ (V p) z = 0 := by
  have h : inner ℂ p (V z) = 0 := by
    calc
      _ = inner ℂ (Q p) (V z) := by rw [hp]
      _ = inner ℂ p (Q (V z)) := hQ _ _
      _ = 0 := by rw [hVz, inner_smul_right_eq_smul]; simp [horth]
  exact ⟨h, (hV p z).trans h⟩

/-- Exact Hilbert-space norm of both private components. -/
theorem kernel_catalyst_norms (V : E →L[ℂ] E)
    (hnorm : ∀ x, ‖V x‖ = ‖x‖) (p z : E)
    (ho₁ : inner ℂ p (V z) = 0) (ho₂ : inner ℂ (V p) z = 0)
    {α τ : ℝ} (hα : 0 < α) (hτ : 0 < τ) :
    ‖Real.sqrt (α * τ) • p + (α / Real.sqrt (α * τ)) • V z‖ ^ 2 =
        α * τ * ‖p‖ ^ 2 + α / τ * ‖z‖ ^ 2 ∧
    ‖Real.sqrt (α * τ) • V p - (α / Real.sqrt (α * τ)) • z‖ ^ 2 =
        α * τ * ‖p‖ ^ 2 + α / τ * ‖z‖ ^ 2 := by
  have hμ : 0 < α * τ := mul_pos hα hτ
  have hg : 0 < Real.sqrt (α * τ) := Real.sqrt_pos.mpr hμ
  have hs : (Real.sqrt (α * τ)) ^ 2 = α * τ := Real.sq_sqrt hμ.le
  have hc : (α / Real.sqrt (α * τ)) ^ 2 = α / τ := by
    rw [div_pow, hs]
    field_simp
  have hi₁ : inner ℂ (Real.sqrt (α * τ) • p)
      ((α / Real.sqrt (α * τ)) • V z) = 0 := by
    simp [inner_smul_left_eq_smul, inner_smul_right_eq_smul, ho₁]
  have hi₂ : inner ℂ (Real.sqrt (α * τ) • V p)
      ((α / Real.sqrt (α * τ)) • z) = 0 := by
    simp [inner_smul_left_eq_smul, inner_smul_right_eq_smul, ho₂]
  constructor
  · rw [norm_add_sq (𝕜 := ℂ)]
    simp only [hi₁, RCLike.zero_re, mul_zero, add_zero]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hg,
      abs_of_pos (div_pos hα hg), hnorm, mul_pow, hs, hc]
  · rw [norm_sub_sq (𝕜 := ℂ)]
    simp only [hi₂, RCLike.zero_re, mul_zero, sub_zero, norm_smul, Real.norm_eq_abs,
      abs_of_pos hg, abs_of_pos (div_pos hα hg), hnorm, mul_pow, hs, hc]

end OptimalQLS
