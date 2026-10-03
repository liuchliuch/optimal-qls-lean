import OptimalQLS.TransducerCompiler.BudgetLayout
import OptimalQLS.TransducerCompiler.Energy

/-! # From weighted reservoir norms to the advertised squared-error budget -/

noncomputable section
namespace OptimalQLS.TransducerCompiler

/-- Normalization turns the reservoir multiplicity `K/J` into a `1/J` error term.
The work bound may include additional nonnegative energy. -/
theorem normalized_weighted_error_sq {K J : ℕ} (hK : 0 < K) (hJ : 0 < J)
    (hdiv : J ∣ K) {E A L₁ L₂ W : ℝ}
    (hE : 0 ≤ E) (hA : 0 ≤ A) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hwork : A + L₁ ≤ W)
    (herror : E ≤ 2 / Real.sqrt (K : ℝ) *
      Real.sqrt (A + L₁ + (K / J : ℕ) * L₂)) :
    E ^ 2 ≤ 4 * (W / K + L₂ / J) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hweight : 0 ≤ A + L₁ + (K / J : ℕ) * L₂ := by positivity
  have hR : 0 ≤ 2 / Real.sqrt (K : ℝ) *
      Real.sqrt (A + L₁ + (K / J : ℕ) * L₂) := by positivity
  have hsq := (sq_le_sq₀ hE hR).2 herror
  rw [mul_pow, div_pow, Real.sq_sqrt hKr.le, Real.sq_sqrt hweight] at hsq
  have hnat : ((K / J : ℕ) : ℝ) = (K : ℝ) / J := Nat.cast_div_charZero hdiv
  rw [hnat] at hsq
  have halg : (2 : ℝ) ^ 2 / K * (A + L₁ + (K : ℝ) / J * L₂) =
      4 * ((A + L₁) / K + L₂ / J) := by
    field_simp [ne_of_gt hKr, ne_of_gt hJr]
    ring
  rw [halg] at hsq
  have hworkdiv := div_le_div_of_nonneg_right hwork hKr.le
  linarith

namespace BudgetParameters

variable {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ)

/-- The exact layout's reservoir bound implies the finite preparation error formula. -/
theorem layout_weighted_error_sq {E A L₁ L₂ W : ℝ}
    (hE : 0 ≤ E) (hA : 0 ≤ A) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hwork : A + L₁ ≤ W)
    (herror : E ≤ 2 / Real.sqrt (mainBudget κ : ℝ) *
      Real.sqrt (A + h.layout.D₁ * L₁ + h.layout.D₂ * L₂)) :
    E ^ 2 ≤ 4 * (W / (mainBudget κ : ℝ) + L₂ / (reflectionBudget κ ŝ : ℝ)) := by
  simp only [layout_D₁, layout_D₂, Nat.cast_one, one_mul] at herror
  exact normalized_weighted_error_sq (mainBudget_pos κ) (reflectionBudget_pos κ ŝ)
    h.reflectionBudget_dvd_mainBudget hE hA hL₁ hL₂ hwork herror

/-- Weighted reservoir control and the source work/query bounds give error below `10⁻³`. -/
theorem finite_error_lt_of_weighted {E A L₁ L₂ W : ℝ}
    (hE : 0 ≤ E) (hA : 0 ≤ A) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hwork : A + L₁ ≤ W) (hW : W ≤ 9 * κ) (hLe : L₂ ≤ κ / (8 * ŝ))
    (herror : E ≤ 2 / Real.sqrt (mainBudget κ : ℝ) *
      Real.sqrt (A + h.layout.D₁ * L₁ + h.layout.D₂ * L₂)) :
    E < (1 : ℝ) / 1000 :=
  h.finite_error_lt hW hLe (h.layout_weighted_error_sq hE hA hL₁ hL₂ hwork herror)

/-- Direct energy formulation for use with the actual compiled circuit's norm estimate. -/
theorem finite_error_lt_of_energy {n : Type*} [Fintype n]
    (v₀ v₁ v₂ : n → ℂ) {E : ℝ} (hE : 0 ≤ E)
    (hW : energy v₀ + energy v₁ + energy v₂ ≤ 9 * κ)
    (hLe : energy v₂ ≤ κ / (8 * ŝ))
    (herror : E ≤ 2 / Real.sqrt (mainBudget κ : ℝ) *
      Real.sqrt (energy v₀ + h.layout.D₁ * energy v₁ + h.layout.D₂ * energy v₂)) :
    E < (1 : ℝ) / 1000 := by
  apply h.finite_error_lt_of_weighted hE (energy_nonneg v₀)
    (energy_nonneg v₁) (energy_nonneg v₂) (W := energy v₀ + energy v₁ + energy v₂)
  · linarith [energy_nonneg v₂]
  · exact hW
  · exact hLe
  · exact herror

end BudgetParameters
end OptimalQLS.TransducerCompiler
