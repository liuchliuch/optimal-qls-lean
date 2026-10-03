import OptimalQLS.TransducerCompiler.ClockLift
import OptimalQLS.TransducerCompiler.Conjugation

noncomputable section
namespace OptimalQLS.TransducerCompiler
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {K : ℕ}

/-- The final circuit is one fixed unitary independent of input and catalyst. -/
def finiteUnitary (b : Layout K) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) : Matrix.unitaryGroup (Space n K) ℂ :=
  (clockLift (clockPrepare b.zero))⁻¹ * (compile b).eval b S U₁ U₂ *
    clockLift (clockPrepare b.zero)

/-- Finite BJY-style implementation theorem for the actual constructed matrix.
The only semantic hypothesis is the legitimate catalyst relation for S. -/
theorem finite_error (b : Layout K) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) (ξ τ v₀ v₁ v₂ : n → ℂ)
    (hS : S.val *ᵥ bundle ξ v₀ (U₁.val *ᵥ v₁) (U₂.val *ᵥ v₂) = bundle τ v₀ v₁ v₂) :
    ‖Matrix.toEuclideanCLM (n := Space n K) (𝕜 := ℂ) (finiteUnitary b S U₁ U₂).val
        (WithLp.toLp 2 (inputState b.zero ξ)) -
      WithLp.toLp 2 (inputState b.zero τ)‖ ≤
      2 / Real.sqrt (K : ℝ) *
        Real.sqrt (energy v₀ + b.D₁ * energy v₁ + b.D₂ * energy v₂) := by
  rw [finiteUnitary, conjugation_error]
  simp only [Matrix.toEuclideanCLM_toLp, prepare_input]
  exact compiled_uniform_error b S U₁ U₂ ξ τ v₀ v₁ v₂ hS

end OptimalQLS.TransducerCompiler
