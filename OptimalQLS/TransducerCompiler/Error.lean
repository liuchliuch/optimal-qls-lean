import OptimalQLS.TransducerCompiler.Circuit
import OptimalQLS.TransducerCompiler.ClockPreparation
import OptimalQLS.TransducerCompiler.Energy

noncomputable section
namespace OptimalQLS.TransducerCompiler
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {K : ℕ}

theorem state_initial (D₁ D₂ : ℕ) (ξ τ v₀ v₁ v₂ q₁ q₂ : n → ℂ) :
    state (K := K) D₁ D₂ 0 ξ τ v₀ v₁ v₂ q₁ q₂ =
      publicState ξ + catalyst D₁ D₂ v₀ v₁ v₂ := by
  ext ⟨⟨i,l⟩,k⟩
  cases l <;> simp [state, publicState, catalyst, track_zero]

theorem state_final (b : Layout K) (ξ τ v₀ v₁ v₂ q₁ q₂ : n → ℂ) :
    state b.D₁ b.D₂ K ξ τ v₀ v₁ v₂ q₁ q₂ =
      publicState (K := K) τ + catalyst b.D₁ b.D₂ v₀ v₁ v₂ := by
  ext ⟨⟨i,l⟩,k⟩
  cases l <;> simp [state, publicState, catalyst, track_final,
    b.divides₁, b.divides₂, k.isLt]

/-- The exact catalytic equation is proved for the actual compiled unitary. -/
theorem compiled_catalytic_equation (b : Layout K) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) (ξ τ v₀ v₁ v₂ : n → ℂ)
    (hS : S.val *ᵥ bundle ξ v₀ (U₁.val *ᵥ v₁) (U₂.val *ᵥ v₂) = bundle τ v₀ v₁ v₂) :
    ((compile b).eval b S U₁ U₂ : Matrix (Space n K) (Space n K) ℂ) *ᵥ
      (publicState ξ + catalyst b.D₁ b.D₂ v₀ v₁ v₂) =
      publicState τ + catalyst b.D₁ b.D₂ v₀ v₁ v₂ := by
  have h := prefix_invariant b S U₁ U₂ ξ τ v₀ v₁ v₂ hS K le_rfl
  simpa only [compile, state_initial, state_final] using h

/-- Uniform-clock implementation error with the exact weighted catalyst energy. -/
theorem compiled_uniform_error (b : Layout K) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) (ξ τ v₀ v₁ v₂ : n → ℂ)
    (hS : S.val *ᵥ bundle ξ v₀ (U₁.val *ᵥ v₁) (U₂.val *ᵥ v₂) = bundle τ v₀ v₁ v₂) :
    let a : ℂ := ((Real.sqrt (K : ℝ))⁻¹ : ℝ)
    let U := (compile b).eval b S U₁ U₂
    ‖Matrix.toEuclideanCLM (n := Space n K) (𝕜 := ℂ) U.val
        (a • WithLp.toLp 2 (publicState ξ)) -
      a • WithLp.toLp 2 (publicState τ)‖ ≤
      2 / Real.sqrt (K : ℝ) *
        Real.sqrt (energy v₀ + b.D₁ * energy v₁ + b.D₂ * energy v₂) := by
  dsimp only
  let a : ℂ := ((Real.sqrt (K : ℝ))⁻¹ : ℝ)
  let U := (compile b).eval b S U₁ U₂
  let x := WithLp.toLp 2 (publicState (K := K) ξ)
  let y := WithLp.toLp 2 (publicState (K := K) τ)
  let v := WithLp.toLp 2 (catalyst (K := K) b.D₁ b.D₂ v₀ v₁ v₂)
  have heq : Matrix.toEuclideanCLM (n := Space n K) (𝕜 := ℂ) U.val (x + v) = y + v := by
    have h := congrArg (WithLp.toLp 2)
      (compiled_catalytic_equation b S U₁ U₂ ξ τ v₀ v₁ v₂ hS)
    exact h
  have hscaled : Matrix.toEuclideanCLM (n := Space n K) (𝕜 := ℂ) U.val
      (a • x + a • v) = a • y + a • v := by
    rw [← smul_add, map_smul, heq, smul_add]
  have hn : ‖v‖ = Real.sqrt (energy v₀ + b.D₁ * energy v₁ + b.D₂ * energy v₂) := by
    rw [← catalyst_norm_sq b.positive b.D₁ b.D₂ b.le₁ b.le₂ v₀ v₁ v₂,
      Real.sqrt_sq (norm_nonneg _)]
  have ha : ‖a‖ = (Real.sqrt (K : ℝ))⁻¹ := by
    simp [a, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h := catalytic_error U (a • x) (a • y) (a • v) hscaled
  rw [norm_smul, ha, hn] at h
  convert h using 1 <;> dsimp [a, x, y, U] <;> ring

end OptimalQLS.TransducerCompiler
