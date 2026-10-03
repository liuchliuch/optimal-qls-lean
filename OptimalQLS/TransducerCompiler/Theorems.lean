import OptimalQLS.TransducerCompiler.Finite
import OptimalQLS.TransducerCompiler.FixedAccuracy

/-!
# Finite transducer compiler endpoints

These theorems establish the actual uniform finite unitary, error, exact
black-box counts, and real matrix-control semantics. The additional synthesis
into a linear number of one- and two-qubit gates is a separate obligation.
-/

noncomputable section
namespace OptimalQLS.TransducerCompiler
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {K : ℕ}

/-- The exact BJY error expression, with W and Li the actual catalyst energies. -/
theorem finite_bjy_error (b : Layout K) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) (ξ τ v₀ v₁ v₂ : n → ℂ)
    (hS : S.val *ᵥ bundle ξ v₀ (U₁.val *ᵥ v₁) (U₂.val *ᵥ v₂) = bundle τ v₀ v₁ v₂) :
    ‖Matrix.toEuclideanCLM (n := Space n K) (𝕜 := ℂ) (finiteUnitary b S U₁ U₂).val
        (WithLp.toLp 2 (inputState b.zero ξ)) - WithLp.toLp 2 (inputState b.zero τ)‖ ≤
      2 / Real.sqrt (K : ℝ) *
        Real.sqrt (‖WithLp.toLp 2 (bundle (0 : n → ℂ) v₀ v₁ v₂)‖ ^ 2 +
          ((b.D₁ : ℝ) - 1) * ‖WithLp.toLp 2 v₁‖ ^ 2 +
          ((b.D₂ : ℝ) - 1) * ‖WithLp.toLp 2 v₂‖ ^ 2) := by
  rw [private_bundle_norm_sq, ← energy_eq_norm_sq, ← energy_eq_norm_sq]
  have he : energy v₀ + energy v₁ + energy v₂ + ((b.D₁ : ℝ) - 1) * energy v₁ +
      ((b.D₂ : ℝ) - 1) * energy v₂ =
      energy v₀ + b.D₁ * energy v₁ + b.D₂ * energy v₂ := by ring
  rw [he]
  exact finite_error b S U₁ U₂ ξ τ v₀ v₁ v₂ hS

/-- Lemma 2.8: a single explicit finite program works for every admissible
input/catalyst pair. No error, query, or existence certificate is assumed. -/
theorem lemma28 {ε W L₁ L₂ : ℝ} (h : FixedAccuracyParameters ε W L₁ L₂)
    (S : Matrix.unitaryGroup (Base n) ℂ) (U₁ U₂ : Matrix.unitaryGroup n ℂ) :
    ∃ c : Circuit,
      (c.workCalls : ℝ) < 32 * W / ε ^ 2 ∧
      (c.firstCalls : ℝ) < 32 * L₁ / ε ^ 2 ∧
      (c.secondCalls : ℝ) < 32 * L₂ / ε ^ 2 ∧
      ∀ ξ τ v₀ v₁ v₂ : n → ℂ,
        S.val *ᵥ bundle ξ v₀ (U₁.val *ᵥ v₁) (U₂.val *ᵥ v₂) = bundle τ v₀ v₁ v₂ →
        energy v₀ + energy v₁ + energy v₂ ≤ W → energy v₁ ≤ L₁ → energy v₂ ≤ L₂ →
        ‖Matrix.toEuclideanCLM (n := Space n (accuracyBudget ε W)) (𝕜 := ℂ)
            (c.eval h.layout S U₁ U₂).val (WithLp.toLp 2 (inputState h.layout.zero ξ)) -
          WithLp.toLp 2 (inputState h.layout.zero τ)‖ < ε := by
  refine ⟨fullCompile h.layout, ?_, ?_, ?_, ?_⟩
  · rw [(fullCompile_counts h.layout).1]
    exact h.count_bounds.1
  · rw [(fullCompile_counts h.layout).2.1]
    exact h.count_bounds.2.1
  · rw [(fullCompile_counts h.layout).2.2]
    exact h.count_bounds.2.2
  · intro ξ τ v₀ v₁ v₂ hS hW h₁ h₂
    rw [fullCompile_eval]
    exact h.error_lt_of_energy v₀ v₁ v₂ (norm_nonneg _) hW h₁ h₂
      (finite_error h.layout S U₁ U₂ ξ τ v₀ v₁ v₂ hS)

/-- A single instruction list is selected before any work matrix, oracle, input,
or catalyst is supplied. This exposes full compiler uniformity in the type. -/
theorem lemma28_uniform {ε W L₁ L₂ : ℝ} (h : FixedAccuracyParameters ε W L₁ L₂) :
    ∃ c : Circuit,
      (c.workCalls : ℝ) < 32 * W / ε ^ 2 ∧
      (c.firstCalls : ℝ) < 32 * L₁ / ε ^ 2 ∧
      (c.secondCalls : ℝ) < 32 * L₂ / ε ^ 2 ∧
      ∀ (S : Matrix.unitaryGroup (Base n) ℂ) (U₁ U₂ : Matrix.unitaryGroup n ℂ)
        (ξ τ v₀ v₁ v₂ : n → ℂ),
        S.val *ᵥ bundle ξ v₀ (U₁.val *ᵥ v₁) (U₂.val *ᵥ v₂) = bundle τ v₀ v₁ v₂ →
        energy v₀ + energy v₁ + energy v₂ ≤ W → energy v₁ ≤ L₁ → energy v₂ ≤ L₂ →
        ‖Matrix.toEuclideanCLM (n := Space n (accuracyBudget ε W)) (𝕜 := ℂ)
            (c.eval h.layout S U₁ U₂).val (WithLp.toLp 2 (inputState h.layout.zero ξ)) -
          WithLp.toLp 2 (inputState h.layout.zero τ)‖ < ε := by
  refine ⟨fullCompile h.layout, ?_, ?_, ?_, ?_⟩
  · rw [(fullCompile_counts h.layout).1]; exact h.count_bounds.1
  · rw [(fullCompile_counts h.layout).2.1]; exact h.count_bounds.2.1
  · rw [(fullCompile_counts h.layout).2.2]; exact h.count_bounds.2.2
  · intro S U₁ U₂ ξ τ v₀ v₁ v₂ hS hW h₁ h₂
    rw [fullCompile_eval]
    exact h.error_lt_of_energy v₀ v₁ v₂ (norm_nonneg _) hW h₁ h₂
      (finite_error h.layout S U₁ U₂ ξ τ v₀ v₁ v₂ hS)

/-- Appendix A.2: the source's actual dyadic choices give error below 10⁻³. -/
theorem appendixA2_error {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ)
    (S : Matrix.unitaryGroup (Base n) ℂ) (U₁ U₂ : Matrix.unitaryGroup n ℂ)
    (ξ τ v₀ v₁ v₂ : n → ℂ)
    (hS : S.val *ᵥ bundle ξ v₀ (U₁.val *ᵥ v₁) (U₂.val *ᵥ v₂) = bundle τ v₀ v₁ v₂)
    (hW : energy v₀ + energy v₁ + energy v₂ ≤ 9 * κ)
    (hL : energy v₂ ≤ κ / (8 * ŝ)) :
    ‖Matrix.toEuclideanCLM (n := Space n (mainBudget κ)) (𝕜 := ℂ)
        ((fullCompile h.layout).eval h.layout S U₁ U₂).val
          (WithLp.toLp 2 (inputState h.layout.zero ξ)) -
      WithLp.toLp 2 (inputState h.layout.zero τ)‖ < (1 : ℝ) / 1000 := by
  rw [fullCompile_eval]
  exact h.finite_error_lt_of_energy v₀ v₁ v₂ (norm_nonneg _) hW hL
    (finite_error h.layout S U₁ U₂ ξ τ v₀ v₁ v₂ hS)

/-- Appendix A.2: exact work/first/second budgets and separate linear bounds. -/
theorem appendixA2_counts {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ) :
    (fullCompile h.layout).workCalls = mainBudget κ ∧
    (fullCompile h.layout).firstCalls = mainBudget κ ∧
    (fullCompile h.layout).secondCalls = reflectionBudget κ ŝ ∧
    ((fullCompile h.layout).firstCalls : ℝ) < 256000000 * κ ∧
    ((fullCompile h.layout).secondCalls : ℝ) < 60000000 * (κ / s) := by
  rw [(fullCompile_counts h.layout).1, (fullCompile_counts h.layout).2.1,
    (fullCompile_counts h.layout).2.2]
  exact ⟨h.layout_exact_counts.1, h.layout_exact_counts.2.1, h.layout_exact_counts.2.2,
    by rw [h.layout_exact_counts.2.1]; exact h.mainBudget_bounds.2,
    by rw [h.layout_exact_counts.2.2]; exact h.reflectionBudget_scale_bound⟩

/-- Compiler routing touches the clock, never the data index or label. -/
theorem routing_preserves_data_label (b : Layout K) (t : ℕ) (x : Space n K) :
    (routing b.zero
      (address b.zero b.D₁ b.D₂ (b.time t) b.positive₁ b.positive₂ b.le₁ b.le₂) x).1 = x.1 := rfl

/-- Appendix A.1's real-coefficient claim for each actual routing matrix. -/
theorem routing_real (b : Layout K) (t : ℕ) (i j : Space n K) :
    ((permutation (routing b.zero
      (address b.zero b.D₁ b.D₂ (b.time t) b.positive₁ b.positive₂ b.le₁ b.le₂))).val i j).im = 0 :=
  permutation_real _ _ _

/-- Appendix A.1's real-coefficient claim for actual clock preparation. -/
theorem preparation_real (b : Layout K) (i j : Space n K) :
    ((clockLift (n := n) (clockPrepare b.zero)).val i j).im = 0 :=
  clockLift_real _ (clockPrepare_real b.zero) i j

end OptimalQLS.TransducerCompiler
