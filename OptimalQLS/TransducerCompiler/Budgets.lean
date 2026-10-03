import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Dyadic budgets for the finite preparation circuit

This file proves the numerical part of Appendix A.2 of the manuscript.
`powerTwoCeil x` is the least natural power of two at least `x`; in
particular this is exactly the ceiling-logarithm convention for `x ≥ 1`.
The compiler and its error estimate are separate from these arithmetic lemmas.
-/

noncomputable section
namespace OptimalQLS.TransducerCompiler

private theorem exists_power_ge (x : ℝ) : ∃ n : ℕ, x ≤ (2 : ℝ) ^ n := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 2)
  exact ⟨n, hn.le⟩

/-- The exponent of the least power of two at least a real target. -/
def powerTwoCeilExponent (x : ℝ) : ℕ := by
  classical
  exact Nat.find (exists_power_ge x)

/-- Dyadic rounding upward, with value one for targets at most one. -/
def powerTwoCeil (x : ℝ) : ℕ := 2 ^ powerTwoCeilExponent x

theorem powerTwoCeil_is_power (x : ℝ) :
    ∃ n : ℕ, powerTwoCeil x = 2 ^ n :=
  ⟨powerTwoCeilExponent x, rfl⟩

theorem powerTwoCeil_pos (x : ℝ) : 0 < powerTwoCeil x := by
  exact pow_pos (by norm_num) _

theorem le_powerTwoCeil (x : ℝ) : x ≤ (powerTwoCeil x : ℝ) := by
  classical
  simpa [powerTwoCeil, powerTwoCeilExponent] using Nat.find_spec (exists_power_ge x)

theorem powerTwoCeil_minimal {x : ℝ} {n : ℕ} (h : x ≤ (2 : ℝ) ^ n) :
    powerTwoCeilExponent x ≤ n := by
  classical
  exact Nat.find_min' (exists_power_ge x) h

theorem powerTwoCeilExponent_mono {x y : ℝ} (h : x ≤ y) :
    powerTwoCeilExponent x ≤ powerTwoCeilExponent y := by
  apply powerTwoCeil_minimal
  simpa [powerTwoCeil] using h.trans (le_powerTwoCeil y)

theorem powerTwoCeil_mono {x y : ℝ} (h : x ≤ y) :
    powerTwoCeil x ≤ powerTwoCeil y := by
  exact Nat.pow_le_pow_right (by norm_num) (powerTwoCeilExponent_mono h)

/-- Dyadic budgets are nested by divisibility, not merely ordered. -/
theorem powerTwoCeil_dvd_of_le {x y : ℝ} (h : x ≤ y) :
    powerTwoCeil x ∣ powerTwoCeil y := by
  exact pow_dvd_pow 2 (powerTwoCeilExponent_mono h)

theorem powerTwoCeil_lt_twice {x : ℝ} (hx : 1 ≤ x) :
    (powerTwoCeil x : ℝ) < 2 * x := by
  classical
  by_cases he : powerTwoCeilExponent x = 0
  · simp [powerTwoCeil, he]
    linarith
  · have hpos : 0 < powerTwoCeilExponent x := Nat.pos_of_ne_zero he
    have hpred : powerTwoCeilExponent x - 1 < powerTwoCeilExponent x :=
      Nat.sub_lt hpos (by norm_num)
    have hmin : (2 : ℝ) ^ (powerTwoCeilExponent x - 1) < x := by
      exact lt_of_not_ge (Nat.find_min (exists_power_ge x) hpred)
    have hsucc : powerTwoCeilExponent x - 1 + 1 = powerTwoCeilExponent x := by omega
    have hpow : (powerTwoCeil x : ℝ) =
        (2 : ℝ) ^ (powerTwoCeilExponent x - 1) * 2 := by
      simp only [powerTwoCeil, Nat.cast_pow, Nat.cast_ofNat]
      conv_lhs => rw [← hsucc, pow_succ]
    rw [hpow]
    linarith

/-- Both the transducer budget `K` and first-oracle budget `K₁`. -/
def mainBudget (κ : ℝ) : ℕ := powerTwoCeil (128000000 * κ)

/-- The first-oracle budget is exactly the total transducer budget. -/
abbrev firstOracleBudget (κ : ℝ) : ℕ := mainBudget κ

@[simp] theorem firstOracleBudget_eq_mainBudget (κ : ℝ) :
    firstOracleBudget κ = mainBudget κ := rfl

/-- The second-oracle budget `K₂`. -/
def reflectionBudget (κ ŝ : ℝ) : ℕ :=
  powerTwoCeil (8000000 * (1 + κ / ŝ))

theorem mainBudget_is_power (κ : ℝ) : ∃ n : ℕ, mainBudget κ = 2 ^ n :=
  powerTwoCeil_is_power _

theorem reflectionBudget_is_power (κ ŝ : ℝ) :
    ∃ n : ℕ, reflectionBudget κ ŝ = 2 ^ n :=
  powerTwoCeil_is_power _

theorem mainBudget_pos (κ : ℝ) : 0 < mainBudget κ := powerTwoCeil_pos _

theorem reflectionBudget_pos (κ ŝ : ℝ) : 0 < reflectionBudget κ ŝ :=
  powerTwoCeil_pos _

/-- The physical parameter assumptions used for the finite preparation circuit. -/
structure BudgetParameters (κ s ŝ : ℝ) : Prop where
  kappa_ge_two : 2 ≤ κ
  scale_ge_one : 1 ≤ s
  scale_le_kappa : s ≤ κ
  estimate_lower : 3 * s / 8 ≤ ŝ
  estimate_upper : ŝ ≤ 5 * s / 2

namespace BudgetParameters

variable {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ)
include h

theorem kappa_pos : 0 < κ := by linarith [h.kappa_ge_two]
theorem scale_pos : 0 < s := by linarith [h.scale_ge_one]
theorem estimate_pos : 0 < ŝ := by
  linarith [h.scale_ge_one, h.estimate_lower]

theorem mainBudget_bounds :
    128000000 * κ ≤ (mainBudget κ : ℝ) ∧
    (mainBudget κ : ℝ) < 256000000 * κ := by
  constructor
  · exact le_powerTwoCeil _
  · have htarget : 1 ≤ 128000000 * κ := by linarith [h.kappa_ge_two]
    have hb := powerTwoCeil_lt_twice htarget
    dsimp [mainBudget]
    linarith

theorem reflectionBudget_bounds :
    8000000 * (1 + κ / ŝ) ≤ (reflectionBudget κ ŝ : ℝ) ∧
    (reflectionBudget κ ŝ : ℝ) < 16000000 * (1 + κ / ŝ) := by
  constructor
  · exact le_powerTwoCeil _
  · have hdiv : 0 ≤ κ / ŝ := div_nonneg h.kappa_pos.le h.estimate_pos.le
    have htarget : 1 ≤ 8000000 * (1 + κ / ŝ) := by linarith
    have hb := powerTwoCeil_lt_twice htarget
    dsimp [reflectionBudget]
    linarith

theorem reflectionTarget_le_mainTarget :
    8000000 * (1 + κ / ŝ) ≤ 128000000 * κ := by
  have hest : (3 : ℝ) / 8 ≤ ŝ := by linarith [h.estimate_lower, h.scale_ge_one]
  have hdiv : κ / ŝ ≤ (8 : ℝ) * κ / 3 := by
    apply (div_le_iff₀ h.estimate_pos).2
    nlinarith [mul_le_mul_of_nonneg_left hest h.kappa_pos.le]
  nlinarith [h.kappa_ge_two]

theorem reflectionBudget_le_mainBudget : reflectionBudget κ ŝ ≤ mainBudget κ :=
  powerTwoCeil_mono h.reflectionTarget_le_mainTarget

theorem reflectionBudget_dvd_mainBudget : reflectionBudget κ ŝ ∣ mainBudget κ :=
  powerTwoCeil_dvd_of_le h.reflectionTarget_le_mainTarget

/-- A fully explicit `O(κ/s)` bound, including dyadic rounding. -/
theorem reflectionBudget_scale_bound :
    (reflectionBudget κ ŝ : ℝ) < 60000000 * (κ / s) := by
  have hs := h.scale_pos
  have he := h.estimate_pos
  have hk := h.kappa_pos
  have hr : 1 ≤ κ / s := (le_div_iff₀ hs).2 (by simpa using h.scale_le_kappa)
  have hratio : κ / ŝ ≤ (8 : ℝ) / 3 * (κ / s) := by
    apply (div_le_iff₀ he).2
    have hlower : 3 * s ≤ 8 * ŝ := by linarith [h.estimate_lower]
    have hprod := mul_le_mul_of_nonneg_left hlower hk.le
    field_simp
    nlinarith
  have hb := h.reflectionBudget_bounds.2
  nlinarith

/-- The exact numerical estimate in Appendix A.2, before taking a square root. -/
theorem finite_error_sq_bound {W Le error : ℝ}
    (hW : W ≤ 9 * κ) (hLe : Le ≤ κ / (8 * ŝ))
    (herror : error ^ 2 ≤ 4 * (W / (mainBudget κ : ℝ) +
      Le / (reflectionBudget κ ŝ : ℝ))) :
    error ^ 2 ≤ (11 : ℝ) / 32000000 := by
  have hK : 0 < (mainBudget κ : ℝ) := by exact_mod_cast powerTwoCeil_pos _
  have hK₂ : 0 < (reflectionBudget κ ŝ : ℝ) := by exact_mod_cast powerTwoCeil_pos _
  have hWratio : W / (mainBudget κ : ℝ) ≤ (9 : ℝ) / 128000000 := by
    apply (div_le_iff₀ hK).2
    nlinarith [h.mainBudget_bounds.1]
  have he := h.estimate_pos
  have hk := h.kappa_pos
  have hLeratio : Le / (reflectionBudget κ ŝ : ℝ) ≤ (1 : ℝ) / 64000000 := by
    apply (div_le_iff₀ hK₂).2
    have hl : Le * (8 * ŝ) ≤ κ := (le_div_iff₀ (by positivity : 0 < 8 * ŝ)).1 hLe
    have hb := h.reflectionBudget_bounds.1
    have hb' : 8000000 * (ŝ + κ) ≤ (reflectionBudget κ ŝ : ℝ) * ŝ := by
      have hbmul := mul_le_mul_of_nonneg_right hb he.le
      field_simp at hbmul
      nlinarith
    nlinarith
  linarith

/-- A compiler satisfying the squared-error estimate has error below `10⁻³`. -/
theorem finite_error_lt {W Le error : ℝ}
    (hW : W ≤ 9 * κ) (hLe : Le ≤ κ / (8 * ŝ))
    (herror : error ^ 2 ≤ 4 * (W / (mainBudget κ : ℝ) +
      Le / (reflectionBudget κ ŝ : ℝ))) :
    error < (1 : ℝ) / 1000 := by
  have hb := h.finite_error_sq_bound hW hLe herror
  nlinarith [sq_nonneg (error - 1 / 1000)]

/-- The two-sided numerical statement, convenient when `error` is not a norm. -/
theorem abs_finite_error_lt {W Le error : ℝ}
    (hW : W ≤ 9 * κ) (hLe : Le ≤ κ / (8 * ŝ))
    (herror : error ^ 2 ≤ 4 * (W / (mainBudget κ : ℝ) +
      Le / (reflectionBudget κ ŝ : ℝ))) :
    |error| < (1 : ℝ) / 1000 := by
  have hb := h.finite_error_sq_bound hW hLe herror
  rw [abs_lt]
  constructor <;> nlinarith [sq_nonneg (error - 1 / 1000),
    sq_nonneg (error + 1 / 1000)]

end BudgetParameters
end OptimalQLS.TransducerCompiler
