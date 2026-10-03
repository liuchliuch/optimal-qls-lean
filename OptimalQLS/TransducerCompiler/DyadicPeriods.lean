import OptimalQLS.TransducerCompiler.FixedAccuracy
import OptimalQLS.TransducerCompiler.CachedCircuit

noncomputable section
namespace OptimalQLS.TransducerCompiler

/-- Exact quotient of nested dyadic budgets. -/
theorem two_pow_div_two_pow {a b : ℕ} (h : b ≤ a) :
    2^a / 2^b = 2^(a-b) := by
  rw [← Nat.pow_sub_mul_pow 2 h]
  simp

abbrev preparationExponent (κ : ℝ) : ℕ := powerTwoCeilExponent (128000000 * κ)
abbrev reflectionExponent (κ ŝ : ℝ) : ℕ := powerTwoCeilExponent (8000000 * (1 + κ / ŝ))
def preparationPeriod (κ ŝ : ℝ) : ℕ := preparationExponent κ - reflectionExponent κ ŝ

namespace BudgetParameters
variable {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ)
include h

theorem reflectionExponent_le : reflectionExponent κ ŝ ≤ preparationExponent κ :=
  powerTwoCeilExponent_mono h.reflectionTarget_le_mainTarget

theorem period_le : preparationPeriod κ ŝ ≤ preparationExponent κ := Nat.sub_le _ _

theorem layout_D₁_dyadic : h.layout.D₁ = 2^(0 : ℕ) := by simp

theorem layout_D₂_dyadic : h.layout.D₂ = 2^(preparationPeriod κ ŝ) := by
  rw [layout_D₂]
  exact two_pow_div_two_pow h.reflectionExponent_le

end BudgetParameters

abbrev accuracyExponent (ε B : ℝ) : ℕ := powerTwoCeilExponent (16 * B / ε ^ 2)
def accuracyPeriod (ε W B : ℝ) : ℕ := accuracyExponent ε W - accuracyExponent ε B

namespace FixedAccuracyParameters
variable {ε W L₁ L₂ : ℝ} (h : FixedAccuracyParameters ε W L₁ L₂)
include h

theorem firstExponent_le : accuracyExponent ε L₁ ≤ accuracyExponent ε W := by
  apply powerTwoCeilExponent_mono
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h.first_le_work (by norm_num))
    (sq_nonneg ε)

theorem secondExponent_le : accuracyExponent ε L₂ ≤ accuracyExponent ε W := by
  apply powerTwoCeilExponent_mono
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h.second_le_work (by norm_num))
    (sq_nonneg ε)

theorem firstPeriod_le : accuracyPeriod ε W L₁ ≤ accuracyExponent ε W := Nat.sub_le _ _
theorem secondPeriod_le : accuracyPeriod ε W L₂ ≤ accuracyExponent ε W := Nat.sub_le _ _

theorem layout_D₁_dyadic : h.layout.D₁ = 2^(accuracyPeriod ε W L₁) := by
  rw [layout_D₁]
  exact two_pow_div_two_pow h.firstExponent_le

theorem layout_D₂_dyadic : h.layout.D₂ = 2^(accuracyPeriod ε W L₂) := by
  rw [layout_D₂]
  exact two_pow_div_two_pow h.secondExponent_le

end FixedAccuracyParameters

/-- The lower-level gate circuit realizes exactly the same three black-box counts. -/
theorem cached_counts_eq_original {ℓ : ℕ} (b : Layout (2^ℓ)) (d₁ d₂ : ℕ)
    (h₁ : b.D₁ = 2^d₁) (h₂ : b.D₂ = 2^d₂) :
    (cachedCompile ℓ d₁ d₂).workCalls = (compile b).workCalls ∧
    (cachedCompile ℓ d₁ d₂).firstCalls = (compile b).firstCalls ∧
    (cachedCompile ℓ d₁ d₂).secondCalls = (compile b).secondCalls := by
  have hd₁ : d₁ ≤ ℓ := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    rw [← h₁]
    exact b.le₁
  have hd₂ : d₂ ≤ ℓ := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    rw [← h₂]
    exact b.le₂
  have hc := cachedCompile_exact_counts ℓ d₁ d₂ hd₁ hd₂
  have ho := compile_exact_counts b
  rw [hc.1, hc.2.1, hc.2.2, ho.1, ho.2.1, ho.2.2, h₁, h₂]
  exact ⟨rfl,rfl,rfl⟩

end OptimalQLS.TransducerCompiler
