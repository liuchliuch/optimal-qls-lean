import OptimalQLS.TransducerCompiler.Complete

/-! # The complete two-oracle finite compiler in BJY Theorem 7.1's exact form -/

noncomputable section
namespace OptimalQLS.TransducerCompiler
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

def dyadicLayout (ℓ k₁ k₂ : ℕ) (h₁ : k₁ ≤ ℓ) (h₂ : k₂ ≤ ℓ) : Layout (2^ℓ) :=
  Layout.ofBudgets (by positivity) (2^k₁) (2^k₂) (by positivity) (by positivity)
    (pow_dvd_pow 2 h₁) (pow_dvd_pow 2 h₂)

/-- Constructive, witness-independent two-oracle compilation, with literal gate
semantics, exactly K/K₁/K₂ black-box calls, and BJY's unrelaxed error formula. -/
theorem bjy71_complete (ℓ k₁ k₂ : ℕ) (h₁ : k₁ ≤ ℓ) (h₂ : k₂ ≤ ℓ) :
    ∃ c : SynthCircuit ℓ,
      c.workCalls = 2^ℓ ∧ c.firstCalls = 2^k₁ ∧ c.secondCalls = 2^k₂ ∧
      c.auxGates ≤ 1110 * 2^ℓ ∧
      ∀ (S : Matrix.unitaryGroup (Base n) ℂ) (U₁ U₂ : Matrix.unitaryGroup n ℂ)
        (ξ τ v₀ v₁ v₂ : n → ℂ),
        S.val *ᵥ bundle ξ v₀ (U₁.val *ᵥ v₁) (U₂.val *ᵥ v₂) = bundle τ v₀ v₁ v₂ →
        ‖WithLp.toLp 2 ((c.eval S U₁ U₂).val *ᵥ synthInput (dyadicLayout ℓ k₁ k₂ h₁ h₂) ξ -
          synthInput (dyadicLayout ℓ k₁ k₂ h₁ h₂) τ)‖ ≤
          2 / Real.sqrt ((2^ℓ : ℕ) : ℝ) *
            Real.sqrt (‖WithLp.toLp 2 (bundle (0 : n → ℂ) v₀ v₁ v₂)‖^2 +
              ((2 : ℝ)^ℓ / (2 : ℝ)^k₁ - 1) * ‖WithLp.toLp 2 v₁‖^2 +
              ((2 : ℝ)^ℓ / (2 : ℝ)^k₂ - 1) * ‖WithLp.toLp 2 v₂‖^2) := by
  let b := dyadicLayout ℓ k₁ k₂ h₁ h₂
  have hd₁ : b.D₁ = 2^(ℓ-k₁) := two_pow_div_two_pow h₁
  have hd₂ : b.D₂ = 2^(ℓ-k₂) := two_pow_div_two_pow h₂
  obtain ⟨c,hw,hf,hs,ha,hg,he⟩ := finite_compiler_uniform (n := n) b (ℓ-k₁) (ℓ-k₂) hd₁ hd₂
  have ho := compile_exact_counts b
  have hx := Layout.ofBudgets_exact_counts (show 0 < 2^ℓ by positivity) (2^k₁) (2^k₂)
    (by positivity) (by positivity) (pow_dvd_pow 2 h₁) (pow_dvd_pow 2 h₂)
  have hf' : c.firstCalls = 2^k₁ := hf.trans (ho.2.1.symm.trans hx.2.1)
  have hs' : c.secondCalls = 2^k₂ := hs.trans (ho.2.2.symm.trans hx.2.2)
  refine ⟨c,hw,hf',hs',ha,?_⟩
  intro S U₁ U₂ ξ τ v₀ v₁ v₂ hS
  have hr₁ : (b.D₁ : ℝ) = (2 : ℝ)^ℓ / (2 : ℝ)^k₁ := by
    change ((2^ℓ / 2^k₁ : ℕ) : ℝ) = _
    rw [Nat.cast_div_charZero (pow_dvd_pow 2 h₁)]
    simp
  have hr₂ : (b.D₂ : ℝ) = (2 : ℝ)^ℓ / (2 : ℝ)^k₂ := by
    change ((2^ℓ / 2^k₂ : ℕ) : ℝ) = _
    rw [Nat.cast_div_charZero (pow_dvd_pow 2 h₂)]
    simp
  have hb := he S U₁ U₂ ξ τ v₀ v₁ v₂ hS
  rw [hr₁,hr₂] at hb
  rw [private_bundle_norm_sq, ← energy_eq_norm_sq, ← energy_eq_norm_sq]
  have halg : energy v₀ + energy v₁ + energy v₂ +
      ((2 : ℝ)^ℓ / (2 : ℝ)^k₁ - 1) * energy v₁ +
      ((2 : ℝ)^ℓ / (2 : ℝ)^k₂ - 1) * energy v₂ =
      energy v₀ + (2 : ℝ)^ℓ / (2 : ℝ)^k₁ * energy v₁ +
        (2 : ℝ)^ℓ / (2 : ℝ)^k₂ * energy v₂ := by ring
  rw [halg]
  exact hb

end OptimalQLS.TransducerCompiler
