import OptimalQLS.TransducerCompiler.EfficientError
import OptimalQLS.TransducerCompiler.DyadicPeriods

/-! # Uniform efficient-compiler endpoints before elementary Toffoli expansion

Every counted reversible primitive is a literal NOT, CNOT, or Toffoli.
The separate gate-synthesis layer expands Toffoli using one reusable clean ancilla.
-/

noncomputable section
namespace OptimalQLS.TransducerCompiler
open Matrix BinaryClock

variable {n : Type*} [Fintype n] [DecidableEq n] {ℓ : ℕ}

/-- Add the two explicitly synthesized tensor-Hadamard clock layers. -/
def CachedCircuit.withClock (c : CachedCircuit ℓ) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) : Matrix.unitaryGroup (CachedSpace n ℓ) ℂ :=
  cacheLift (toBitUnitary ((clockLift (HadamardClock.finHadamard ℓ))⁻¹)) *
    c.eval S U₁ U₂ * cacheLift (toBitUnitary (clockLift (HadamardClock.finHadamard ℓ)))

/-- One physical instruction list, selected before all work matrices and input oracles,
with uniform accuracy, exact clean-cache semantics, and linear primitive overhead. -/
theorem lemma28_cached_uniform {ε W L₁ L₂ : ℝ} (h : FixedAccuracyParameters ε W L₁ L₂) :
    ∃ c : CachedCircuit (accuracyExponent ε W),
      (c.workCalls : ℝ) < 32 * W / ε ^ 2 ∧
      (c.firstCalls : ℝ) < 32 * L₁ / ε ^ 2 ∧
      (c.secondCalls : ℝ) < 32 * L₂ / ε ^ 2 ∧
      c.primitiveGates + 2 * accuracyExponent ε W ≤ 74 * accuracyBudget ε W ∧
      ∀ (S : Matrix.unitaryGroup (Base n) ℂ) (U₁ U₂ : Matrix.unitaryGroup n ℂ)
        (ξ τ v₀ v₁ v₂ : n → ℂ),
        S.val *ᵥ bundle ξ v₀ (U₁.val *ᵥ v₁) (U₂.val *ᵥ v₂) = bundle τ v₀ v₁ v₂ →
        energy v₀ + energy v₁ + energy v₂ ≤ W → energy v₁ ≤ L₁ → energy v₂ ≤ L₂ →
        ‖WithLp.toLp 2 ((c.withClock S U₁ U₂).val *ᵥ cachedInput h.layout ξ -
          cachedInput h.layout τ)‖ < ε := by
  let d₁ := accuracyPeriod ε W L₁
  let d₂ := accuracyPeriod ε W L₂
  let c := cachedCompile (accuracyExponent ε W) d₁ d₂
  have hc := cached_counts_eq_original h.layout d₁ d₂ h.layout_D₁_dyadic h.layout_D₂_dyadic
  refine ⟨c, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show c.workCalls = (compile h.layout).workCalls from hc.1]
    exact h.count_bounds.1
  · rw [show c.firstCalls = (compile h.layout).firstCalls from hc.2.1]
    exact h.count_bounds.2.1
  · rw [show c.secondCalls = (compile h.layout).secondCalls from hc.2.2]
    exact h.count_bounds.2.2
  · simpa only [HadamardClock.circuit_gateCount] using
      cachedFinite_primitive_bound (accuracyExponent ε W) d₁ d₂
  · intro S U₁ U₂ ξ τ v₀ v₁ v₂ hS hW hL₁ hL₂
    exact h.error_lt_of_energy v₀ v₁ v₂ (norm_nonneg _) hW hL₁ hL₂
      (cachedFinite_error h.layout d₁ d₂ h.layout_D₁_dyadic h.layout_D₂_dyadic
        S U₁ U₂ ξ τ v₀ v₁ v₂ hS)

/-- The gate-efficient preparation implementation has the source's explicit separate budgets. -/
theorem appendixA2_cached_uniform {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ) :
    ∃ c : CachedCircuit (preparationExponent κ),
      c.workCalls = mainBudget κ ∧ c.firstCalls = mainBudget κ ∧
      c.secondCalls = reflectionBudget κ ŝ ∧
      (c.firstCalls : ℝ) < 256000000 * κ ∧
      (c.secondCalls : ℝ) < 60000000 * (κ / s) ∧
      c.primitiveGates + 2 * preparationExponent κ ≤ 74 * mainBudget κ ∧
      ∀ (S : Matrix.unitaryGroup (Base n) ℂ) (U₁ U₂ : Matrix.unitaryGroup n ℂ)
        (ξ τ v₀ v₁ v₂ : n → ℂ),
        S.val *ᵥ bundle ξ v₀ (U₁.val *ᵥ v₁) (U₂.val *ᵥ v₂) = bundle τ v₀ v₁ v₂ →
        energy v₀ + energy v₁ + energy v₂ ≤ 9 * κ → energy v₂ ≤ κ / (8 * ŝ) →
        ‖WithLp.toLp 2 ((c.withClock S U₁ U₂).val *ᵥ cachedInput h.layout ξ -
          cachedInput h.layout τ)‖ < (1 : ℝ) / 1000 := by
  let d₂ := preparationPeriod κ ŝ
  let c := cachedCompile (preparationExponent κ) 0 d₂
  have hc := cached_counts_eq_original h.layout 0 d₂ h.layout_D₁_dyadic h.layout_D₂_dyadic
  have hw : c.workCalls = mainBudget κ := hc.1.trans h.layout_exact_counts.1
  have hf : c.firstCalls = mainBudget κ := hc.2.1.trans h.layout_exact_counts.2.1
  have hs : c.secondCalls = reflectionBudget κ ŝ := hc.2.2.trans h.layout_exact_counts.2.2
  refine ⟨c, hw, hf, hs, ?_, ?_, ?_, ?_⟩
  · rw [hf]; exact h.mainBudget_bounds.2
  · rw [hs]; exact h.reflectionBudget_scale_bound
  · simpa only [HadamardClock.circuit_gateCount] using
      cachedFinite_primitive_bound (preparationExponent κ) 0 d₂
  · intro S U₁ U₂ ξ τ v₀ v₁ v₂ hS hW hL
    exact h.finite_error_lt_of_energy v₀ v₁ v₂ (norm_nonneg _) hW hL
      (cachedFinite_error h.layout 0 d₂ h.layout_D₁_dyadic h.layout_D₂_dyadic
        S U₁ U₂ ξ τ v₀ v₁ v₂ hS)

end OptimalQLS.TransducerCompiler
