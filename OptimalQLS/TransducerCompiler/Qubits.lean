import OptimalQLS.TransducerCompiler.FixedAccuracy
import OptimalQLS.TransducerCompiler.ReservoirClock
import Mathlib.Algebra.Order.Floor.Semiring

/-! # Explicit logarithmic compiler register sizes -/

noncomputable section
namespace OptimalQLS.TransducerCompiler
open BinaryClock

/-- Two label bits, two ℓ-bit clock/cache registers, and one reusable synthesis ancilla. -/
def auxiliaryQubits (ℓ : ℕ) : ℕ := 2 * ℓ + 3

/-- The physical wire type has exactly the advertised number of qubits. -/
theorem auxiliary_wire_count (ℓ : ℕ) :
    Fintype.card (Option (LabelWire ℓ)) = auxiliaryQubits ℓ := by
  simp [LabelWire, Wire, auxiliaryQubits]
  omega

theorem auxiliary_basis_count (ℓ : ℕ) :
    Fintype.card (Option (LabelWire ℓ) → Bool) = 2 ^ auxiliaryQubits ℓ := by
  simp [Fintype.card_fun, auxiliary_wire_count, auxiliaryQubits]; omega

/-- Upward dyadic exponents are bounded by the ordinary binary logarithm. -/
theorem powerTwoCeilExponent_le_log (x : ℝ) :
    powerTwoCeilExponent x ≤ Nat.log2 ⌈x⌉₊ + 1 := by
  apply powerTwoCeil_minimal
  have h := Nat.lt_log2_self (n := ⌈x⌉₊)
  have hr : (⌈x⌉₊ : ℝ) < (2 : ℝ) ^ (Nat.log2 ⌈x⌉₊ + 1) := by exact_mod_cast h
  exact (Nat.le_ceil x).trans hr.le

/-- The preparation clock needs at most 28 plus log₂⌈κ⌉ binary positions. -/
theorem preparation_clock_width {κ : ℝ} (hκ : 0 ≤ κ) :
    powerTwoCeilExponent (128000000 * κ) ≤ 28 + Nat.log2 ⌈κ⌉₊ := by
  have hmain : powerTwoCeilExponent (128000000 * κ) ≤ 27 + powerTwoCeilExponent κ := by
    apply powerTwoCeil_minimal
    rw [pow_add]
    have hc : (128000000 : ℝ) ≤ 2 ^ (27 : ℕ) := by norm_num
    have hk : κ ≤ (2 : ℝ) ^ powerTwoCeilExponent κ := by
      simpa [powerTwoCeil] using le_powerTwoCeil κ
    exact (mul_le_mul_of_nonneg_right hc hκ).trans
      (mul_le_mul_of_nonneg_left hk (by positivity))
  have hlog := powerTwoCeilExponent_le_log κ
  omega

/-- Explicit version of the preparation compiler's O(log κ) auxiliary-qubit bound. -/
theorem preparation_auxiliary_width {κ : ℝ} (hκ : 0 ≤ κ) :
    auxiliaryQubits (powerTwoCeilExponent (128000000 * κ)) ≤
      2 * Nat.log2 ⌈κ⌉₊ + 59 := by
  have h := preparation_clock_width hκ
  simp only [auxiliaryQubits]
  omega

/-- A fixed accuracy contributes only an additive constant to clock-register width. -/
theorem accuracy_clock_width {ε W : ℝ} (hε : 0 < ε) (hW : 0 ≤ W) :
    powerTwoCeilExponent (16 * W / ε ^ 2) ≤
      powerTwoCeilExponent (16 / ε ^ 2) + Nat.log2 ⌈W⌉₊ + 1 := by
  have hm : powerTwoCeilExponent (16 * W / ε ^ 2) ≤
      powerTwoCeilExponent (16 / ε ^ 2) + powerTwoCeilExponent W := by
    apply powerTwoCeil_minimal
    rw [pow_add]
    have h₁ : 16 / ε ^ 2 ≤ (2 : ℝ) ^ powerTwoCeilExponent (16 / ε ^ 2) := by
      simpa [powerTwoCeil] using le_powerTwoCeil (16 / ε ^ 2)
    have h₂ : W ≤ (2 : ℝ) ^ powerTwoCeilExponent W := by
      simpa [powerTwoCeil] using le_powerTwoCeil W
    calc
      16 * W / ε ^ 2 = (16 / ε ^ 2) * W := by ring
      _ ≤ (2 : ℝ) ^ powerTwoCeilExponent (16 / ε ^ 2) *
          (2 : ℝ) ^ powerTwoCeilExponent W :=
        mul_le_mul h₁ h₂ hW (by positivity)
  have hlog := powerTwoCeilExponent_le_log W
  omega

end OptimalQLS.TransducerCompiler
