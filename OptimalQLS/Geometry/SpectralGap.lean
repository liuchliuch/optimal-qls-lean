import OptimalQLS.Geometry.Diagonal
import Mathlib.Tactic.LinearCombination

noncomputable section
namespace OptimalQLS.Geometry
variable {ι : Type*} [Fintype ι]

/-- Every nonzero eigenvalue of the actual auxiliary operator comes from
one of the explicit quadratic blocks. -/
theorem auxiliary_eigenvalue_square (a : ι → ℝ) (t : ℝ) {μ : ℂ}
    (hμ : μ ≠ 0) {x : Triple ι} (hx : x ≠ 0)
    (heig : auxiliary a t x = μ • x) :
    ∃ i, μ ^ 2 = (a i : ℂ) ^ 2 + (t : ℂ) ^ 2 := by
  classical
  have hcoord (j : Fin 3) (i : ι) := congrArg (fun v : Triple ι => v (j,i)) heig
  have hx0 : ∃ i, x (0,i) ≠ 0 := by
    by_contra! hzero
    apply hx
    ext ⟨j,i⟩
    fin_cases j
    · exact hzero i
    · have h := hcoord 1 i
      simp [hzero i] at h
      exact h.resolve_left hμ
    · have h := hcoord 2 i
      simp [hzero i] at h
      exact h.resolve_left hμ
  obtain ⟨i,hi⟩ := hx0
  refine ⟨i, ?_⟩
  have h₀ := hcoord 0 i
  have h₁ := hcoord 1 i
  have h₂ := hcoord 2 i
  simp only [auxiliary_zero, auxiliary_one, auxiliary_two, PiLp.smul_apply,
    smul_eq_mul] at h₀ h₁ h₂
  apply mul_right_cancel₀ hi
  linear_combination -(μ * h₀) - (a i : ℂ) * h₁ + (t : ℂ) * h₂

/-- Full nonzero spectral-gap conclusion in the L2 setting, for complex
eigenvalues (not only eigenvalues assumed real). -/
theorem auxiliary_spectral_gap (a : ι → ℝ) {t : ℝ} (ht : 0 < t)
    (ha : ∀ i, t ≤ |a i| ∧ |a i| ≤ 1) {μ : ℂ} (hμ : μ ≠ 0)
    (heig : Module.End.HasEigenvalue (auxiliary a t).toLinearMap μ) :
    Real.sqrt 2 * t ≤ ‖μ‖ ∧ ‖μ‖ ≤ Real.sqrt (1 + t ^ 2) := by
  obtain ⟨x, hxmem, hxne⟩ := heig.exists_hasEigenvector
  have hx : auxiliary a t x = μ • x := by
    exact Module.End.mem_eigenspace_iff.mp hxmem
  obtain ⟨i, hi⟩ := auxiliary_eigenvalue_square a t hμ hxne hx
  have hnorm : ‖μ‖ ^ 2 = a i ^ 2 + t ^ 2 := by
    have h := congrArg norm hi
    have hc : (a i : ℂ)^2 + (t : ℂ)^2 = ((a i ^ 2 + t ^ 2 : ℝ) : ℂ) := by
      push_cast; rfl
    rw [hc, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (denominator_pos ht)] at h
    exact h
  have hs : ‖μ‖ = Real.sqrt (a i ^ 2 + t ^ 2) := by
    rw [← hnorm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg μ)]
  rw [hs]
  exact auxiliary_eigenvalue_bounds ht (ha i).1 (ha i).2

end OptimalQLS.Geometry
