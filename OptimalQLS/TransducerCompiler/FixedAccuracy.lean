import OptimalQLS.TransducerCompiler.AlgebraicError

/-!
# Explicit fixed-accuracy compiler budgets

This file supplies the uniform numerical budgets for Lemma 2.8.
It proves actual program call counts and the numerical implication of the
weighted-reservoir estimate. Gate synthesis is not part of these statements.
-/

noncomputable section
namespace OptimalQLS.TransducerCompiler

/-- Upward dyadic rounding with a fixed margin in the squared-error budget. -/
def accuracyBudget (ε B : ℝ) : ℕ := powerTwoCeil (16 * B / ε ^ 2)

theorem accuracyBudget_pos (ε B : ℝ) : 0 < accuracyBudget ε B := powerTwoCeil_pos _

theorem accuracyBudget_is_power (ε B : ℝ) :
    ∃ n : ℕ, accuracyBudget ε B = 2 ^ n := powerTwoCeil_is_power _

theorem accuracyBudget_bounds {ε B : ℝ} (hε : 0 < ε) (hεone : ε < 1) (hB : 1 ≤ B) :
    16 * B / ε ^ 2 ≤ (accuracyBudget ε B : ℝ) ∧
    (accuracyBudget ε B : ℝ) < 32 * B / ε ^ 2 := by
  constructor
  · exact le_powerTwoCeil _
  · have hsq : 0 < ε ^ 2 := sq_pos_of_pos hε
    have htarget : 1 ≤ 16 * B / ε ^ 2 := by
      apply (le_div_iff₀ hsq).2
      nlinarith
    calc
      (accuracyBudget ε B : ℝ) < 2 * (16 * B / ε ^ 2) := powerTwoCeil_lt_twice htarget
      _ = 32 * B / ε ^ 2 := by ring

/-- The uniform work and two oracle bounds of the fixed-accuracy lemma. -/
structure FixedAccuracyParameters (ε W L₁ L₂ : ℝ) : Prop where
  epsilon_pos : 0 < ε
  epsilon_lt_one : ε < 1
  first_ge_one : 1 ≤ L₁
  second_ge_one : 1 ≤ L₂
  first_le_work : L₁ ≤ W
  second_le_work : L₂ ≤ W

namespace FixedAccuracyParameters

variable {ε W L₁ L₂ : ℝ} (h : FixedAccuracyParameters ε W L₁ L₂)
include h

theorem work_ge_one : 1 ≤ W := h.first_ge_one.trans h.first_le_work

theorem workBudget_bounds :
    16 * W / ε ^ 2 ≤ (accuracyBudget ε W : ℝ) ∧
    (accuracyBudget ε W : ℝ) < 32 * W / ε ^ 2 :=
  accuracyBudget_bounds h.epsilon_pos h.epsilon_lt_one h.work_ge_one

theorem firstBudget_bounds :
    16 * L₁ / ε ^ 2 ≤ (accuracyBudget ε L₁ : ℝ) ∧
    (accuracyBudget ε L₁ : ℝ) < 32 * L₁ / ε ^ 2 :=
  accuracyBudget_bounds h.epsilon_pos h.epsilon_lt_one h.first_ge_one

theorem secondBudget_bounds :
    16 * L₂ / ε ^ 2 ≤ (accuracyBudget ε L₂ : ℝ) ∧
    (accuracyBudget ε L₂ : ℝ) < 32 * L₂ / ε ^ 2 :=
  accuracyBudget_bounds h.epsilon_pos h.epsilon_lt_one h.second_ge_one

theorem firstBudget_dvd_workBudget : accuracyBudget ε L₁ ∣ accuracyBudget ε W := by
  apply powerTwoCeil_dvd_of_le
  apply div_le_div_of_nonneg_right _ (sq_nonneg ε)
  linarith [h.first_le_work]

theorem secondBudget_dvd_workBudget : accuracyBudget ε L₂ ∣ accuracyBudget ε W := by
  apply powerTwoCeil_dvd_of_le
  apply div_le_div_of_nonneg_right _ (sq_nonneg ε)
  linarith [h.second_le_work]

theorem firstBudget_le_workBudget : accuracyBudget ε L₁ ≤ accuracyBudget ε W :=
  Nat.le_of_dvd (accuracyBudget_pos ε W) h.firstBudget_dvd_workBudget

theorem secondBudget_le_workBudget : accuracyBudget ε L₂ ≤ accuracyBudget ε W :=
  Nat.le_of_dvd (accuracyBudget_pos ε W) h.secondBudget_dvd_workBudget

/-- One concrete instruction schedule, determined only by the uniform bounds. -/
def layout : Layout (accuracyBudget ε W) :=
  Layout.ofBudgets (accuracyBudget_pos ε W) (accuracyBudget ε L₁) (accuracyBudget ε L₂)
    (accuracyBudget_pos ε L₁) (accuracyBudget_pos ε L₂)
    h.firstBudget_dvd_workBudget h.secondBudget_dvd_workBudget

@[simp] theorem layout_D₁ : h.layout.D₁ = accuracyBudget ε W / accuracyBudget ε L₁ := rfl
@[simp] theorem layout_D₂ : h.layout.D₂ = accuracyBudget ε W / accuracyBudget ε L₂ := rfl

/-- Exact syntactic calls to work and the two independent input oracles. -/
theorem exact_counts :
    (compile h.layout).workCalls = accuracyBudget ε W ∧
    (compile h.layout).firstCalls = accuracyBudget ε L₁ ∧
    (compile h.layout).secondCalls = accuracyBudget ε L₂ :=
  Layout.ofBudgets_exact_counts (accuracyBudget_pos ε W) (accuracyBudget ε L₁)
    (accuracyBudget ε L₂) (accuracyBudget_pos ε L₁) (accuracyBudget_pos ε L₂)
    h.firstBudget_dvd_workBudget h.secondBudget_dvd_workBudget

/-- Explicit constants in the fixed-accuracy work/query call bounds. -/
theorem count_bounds :
    ((compile h.layout).workCalls : ℝ) < 32 * W / ε ^ 2 ∧
    ((compile h.layout).firstCalls : ℝ) < 32 * L₁ / ε ^ 2 ∧
    ((compile h.layout).secondCalls : ℝ) < 32 * L₂ / ε ^ 2 := by
  rw [h.exact_counts.1, h.exact_counts.2.1, h.exact_counts.2.2]
  exact ⟨h.workBudget_bounds.2, h.firstBudget_bounds.2, h.secondBudget_bounds.2⟩

/-- The same chosen budgets work for every admissible collection of catalyst energies. -/
theorem error_lt {E A B₁ B₂ : ℝ} (hE : 0 ≤ E)
    (hA : 0 ≤ A) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hwork : A + B₁ + B₂ ≤ W) (hfirst : B₁ ≤ L₁) (hsecond : B₂ ≤ L₂)
    (herror : E ≤ 2 / Real.sqrt (accuracyBudget ε W : ℝ) *
      Real.sqrt (A + h.layout.D₁ * B₁ + h.layout.D₂ * B₂)) :
    E < ε := by
  have hK : (0 : ℝ) < accuracyBudget ε W := by exact_mod_cast accuracyBudget_pos ε W
  have hK₁ : (0 : ℝ) < accuracyBudget ε L₁ := by exact_mod_cast accuracyBudget_pos ε L₁
  have hK₂ : (0 : ℝ) < accuracyBudget ε L₂ := by exact_mod_cast accuracyBudget_pos ε L₂
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos h.epsilon_pos
  have hweight : 0 ≤ A + h.layout.D₁ * B₁ + h.layout.D₂ * B₂ := by positivity
  have hR : 0 ≤ 2 / Real.sqrt (accuracyBudget ε W : ℝ) *
      Real.sqrt (A + h.layout.D₁ * B₁ + h.layout.D₂ * B₂) := by positivity
  have hsq := (sq_le_sq₀ hE hR).2 herror
  rw [mul_pow, div_pow, Real.sq_sqrt hK.le, Real.sq_sqrt hweight] at hsq
  simp only [layout_D₁, layout_D₂,
    Nat.cast_div_charZero h.firstBudget_dvd_workBudget,
    Nat.cast_div_charZero h.secondBudget_dvd_workBudget] at hsq
  have halg : (2 : ℝ) ^ 2 / accuracyBudget ε W *
      (A + (accuracyBudget ε W : ℝ) / accuracyBudget ε L₁ * B₁ +
        (accuracyBudget ε W : ℝ) / accuracyBudget ε L₂ * B₂) =
      4 * (A / accuracyBudget ε W + B₁ / accuracyBudget ε L₁ + B₂ / accuracyBudget ε L₂) := by
    field_simp [ne_of_gt hK, ne_of_gt hK₁, ne_of_gt hK₂]
    ring
  rw [halg] at hsq
  have hWA : A / accuracyBudget ε W ≤ ε ^ 2 / 16 := by
    apply (div_le_iff₀ hK).2
    have hb := (div_le_iff₀ hεsq).1 h.workBudget_bounds.1
    nlinarith
  have hWB₁ : B₁ / accuracyBudget ε L₁ ≤ ε ^ 2 / 16 := by
    apply (div_le_iff₀ hK₁).2
    have hb := (div_le_iff₀ hεsq).1 h.firstBudget_bounds.1
    nlinarith
  have hWB₂ : B₂ / accuracyBudget ε L₂ ≤ ε ^ 2 / 16 := by
    apply (div_le_iff₀ hK₂).2
    have hb := (div_le_iff₀ hεsq).1 h.secondBudget_bounds.1
    nlinarith
  have hstrict : E ^ 2 < ε ^ 2 := by nlinarith
  exact (sq_lt_sq₀ hE h.epsilon_pos.le).1 hstrict

/-- Convenience version for the Euclidean energies of an actual catalyst. -/
theorem error_lt_of_energy {n : Type*} [Fintype n]
    (v₀ v₁ v₂ : n → ℂ) {E : ℝ} (hE : 0 ≤ E)
    (hwork : energy v₀ + energy v₁ + energy v₂ ≤ W)
    (hfirst : energy v₁ ≤ L₁) (hsecond : energy v₂ ≤ L₂)
    (herror : E ≤ 2 / Real.sqrt (accuracyBudget ε W : ℝ) *
      Real.sqrt (energy v₀ + h.layout.D₁ * energy v₁ + h.layout.D₂ * energy v₂)) :
    E < ε :=
  h.error_lt hE (energy_nonneg v₀) (energy_nonneg v₁) (energy_nonneg v₂)
    hwork hfirst hsecond herror

end FixedAccuracyParameters
end OptimalQLS.TransducerCompiler
