import OptimalQLS.TransducerCompiler.Complete

/-! # Complete endpoints for Lemma 2.8 and Appendices A.1–A.2 -/

noncomputable section
namespace OptimalQLS.TransducerCompiler
open Matrix BinaryClock

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Lemma 2.8 with a single literal synthesized circuit before all oracle/catalyst
quantifiers, exact separate budgets, and linear real auxiliary-gate overhead. -/
theorem lemma28_complete {ε W L₁ L₂ : ℝ} (h : FixedAccuracyParameters ε W L₁ L₂) :
    ∃ c : SynthCircuit (accuracyExponent ε W),
      c.workCalls = accuracyBudget ε W ∧
      c.firstCalls = accuracyBudget ε L₁ ∧ c.secondCalls = accuracyBudget ε L₂ ∧
      (c.firstCalls : ℝ) < 32 * L₁ / ε^2 ∧ (c.secondCalls : ℝ) < 32 * L₂ / ε^2 ∧
      c.auxGates ≤ 1110 * accuracyBudget ε W ∧
      (∀ g : ℕ, c.chargedGates g ≤ (1110+g) * accuracyBudget ε W) ∧
      ∀ (S : Matrix.unitaryGroup (Base n) ℂ) (U₁ U₂ : Matrix.unitaryGroup n ℂ)
        (ξ τ v₀ v₁ v₂ : n → ℂ),
        S.val *ᵥ bundle ξ v₀ (U₁.val *ᵥ v₁) (U₂.val *ᵥ v₂) = bundle τ v₀ v₁ v₂ →
        energy v₀ + energy v₁ + energy v₂ ≤ W → energy v₁ ≤ L₁ → energy v₂ ≤ L₂ →
        ‖WithLp.toLp 2 ((c.eval S U₁ U₂).val *ᵥ synthInput h.layout ξ -
          synthInput h.layout τ)‖ < ε := by
  obtain ⟨c,hw,hf,hs,ha,hg,he⟩ := finite_compiler_uniform (n := n) h.layout
    (accuracyPeriod ε W L₁) (accuracyPeriod ε W L₂) h.layout_D₁_dyadic h.layout_D₂_dyadic
  have ho := compile_exact_counts h.layout
  have hf' : c.firstCalls = accuracyBudget ε L₁ :=
    hf.trans (ho.2.1.symm.trans h.exact_counts.2.1)
  have hs' : c.secondCalls = accuracyBudget ε L₂ :=
    hs.trans (ho.2.2.symm.trans h.exact_counts.2.2)
  refine ⟨c,hw,hf',hs',?_,?_,ha,hg,?_⟩
  · rw [hf']; exact h.firstBudget_bounds.2
  · rw [hs']; exact h.secondBudget_bounds.2
  · intro S U₁ U₂ ξ τ v₀ v₁ v₂ hS hW h₁ h₂
    exact h.error_lt_of_energy v₀ v₁ v₂ (norm_nonneg _) hW h₁ h₂
      (he S U₁ U₂ ξ τ v₀ v₁ v₂ hS)

/-- Appendix A.2's power-of-two budgets, sharp accuracy, and separate linear query costs,
now for the fully synthesized real elementary auxiliary circuit. -/
theorem appendixA2_complete {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ) :
    ∃ c : SynthCircuit (preparationExponent κ),
      c.workCalls = mainBudget κ ∧ c.firstCalls = mainBudget κ ∧
      c.secondCalls = reflectionBudget κ ŝ ∧
      (c.firstCalls : ℝ) < 256000000 * κ ∧
      (c.secondCalls : ℝ) < 60000000 * (κ / s) ∧
      c.auxGates ≤ 1110 * mainBudget κ ∧
      (∀ g : ℕ, c.chargedGates g ≤ (1110+g) * mainBudget κ) ∧
      ∀ (S : Matrix.unitaryGroup (Base n) ℂ) (U₁ U₂ : Matrix.unitaryGroup n ℂ)
        (ξ τ v₀ v₁ v₂ : n → ℂ),
        S.val *ᵥ bundle ξ v₀ (U₁.val *ᵥ v₁) (U₂.val *ᵥ v₂) = bundle τ v₀ v₁ v₂ →
        energy v₀ + energy v₁ + energy v₂ ≤ 9 * κ → energy v₂ ≤ κ / (8 * ŝ) →
        ‖WithLp.toLp 2 ((c.eval S U₁ U₂).val *ᵥ synthInput h.layout ξ -
          synthInput h.layout τ)‖ < (1 : ℝ) / 1000 := by
  obtain ⟨c,hw,hf,hs,ha,hg,he⟩ := finite_compiler_uniform (n := n) h.layout
    0 (preparationPeriod κ ŝ) h.layout_D₁_dyadic h.layout_D₂_dyadic
  have ho := compile_exact_counts h.layout
  have hf' : c.firstCalls = mainBudget κ := hf.trans (ho.2.1.symm.trans h.layout_exact_counts.2.1)
  have hs' : c.secondCalls = reflectionBudget κ ŝ := hs.trans (ho.2.2.symm.trans h.layout_exact_counts.2.2)
  refine ⟨c,hw,hf',hs',?_,?_,ha,hg,?_⟩
  · rw [hf']; exact h.mainBudget_bounds.2
  · rw [hs']; exact h.reflectionBudget_scale_bound
  · intro S U₁ U₂ ξ τ v₀ v₁ v₂ hS hW hL
    exact h.finite_error_lt_of_energy v₀ v₁ v₂ (norm_nonneg _) hW hL
      (he S U₁ U₂ ξ τ v₀ v₁ v₂ hS)

/-- Actual Hilbert-space dimension of the compiler's physical auxiliary wires. -/
theorem synthSpace_card (ℓ : ℕ) :
    Fintype.card (SynthSpace n ℓ) = Fintype.card n * 2 ^ auxiliaryQubits ℓ := by
  have hl : Fintype.card Label = 4 := by decide
  simp [SynthSpace, CachedSpace, Base, Bits, auxiliaryQubits, hl, pow_add, pow_mul]
  have hp : (2 : ℕ)^ℓ * 2^ℓ = 4^ℓ := by rw [← mul_pow]; norm_num
  rw [hp]
  ring

/-- The complete preparation implementation uses at most 2 log₂⌈κ⌉+59 auxiliary qubits. -/
theorem appendixA2_qubits {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ) :
    auxiliaryQubits (preparationExponent κ) ≤ 2 * Nat.log2 ⌈κ⌉₊ + 59 :=
  preparation_auxiliary_width h.kappa_pos.le

/-- Fixed accuracy affects only the additive constant in auxiliary-register width. -/
theorem lemma28_qubits {ε W L₁ L₂ : ℝ} (h : FixedAccuracyParameters ε W L₁ L₂) :
    auxiliaryQubits (accuracyExponent ε W) ≤
      2 * Nat.log2 ⌈W⌉₊ + 2 * powerTwoCeilExponent (16 / ε^2) + 5 := by
  have hw : 0 ≤ W := by linarith [h.work_ge_one]
  have hb := accuracy_clock_width h.epsilon_pos hw
  simp only [auxiliaryQubits, accuracyExponent]
  omega

end OptimalQLS.TransducerCompiler
