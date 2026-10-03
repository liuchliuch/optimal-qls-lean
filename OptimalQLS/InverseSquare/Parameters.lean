import OptimalQLS.InverseSquare.Accuracy

/-! # Exact spectral-gap and accuracy parameter choices -/
noncomputable section
namespace OptimalQLS.InverseSquare
open Polynomial

def geometricOrder (δ : ℝ) : ℕ := ⌊(δ ^ 2)⁻¹⌋₊

theorem geometricOrder_upper {δ : ℝ} (hδ : 0 < δ) :
    δ ^ 2 * (geometricOrder δ : ℝ) ≤ 1 := by
  have h := Nat.floor_le (show 0 ≤ (δ ^ 2)⁻¹ by positivity)
  have hp := mul_le_mul_of_nonneg_left h (sq_nonneg δ)
  rw [mul_inv_cancel₀ (ne_of_gt (sq_pos_of_pos hδ))] at hp
  exact hp

theorem geometricOrder_lower {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    (3 / 4 : ℝ) ≤ δ ^ 2 * (geometricOrder δ : ℝ) := by
  have h := Nat.lt_floor_add_one ((δ ^ 2)⁻¹)
  have hp := mul_lt_mul_of_pos_left h (sq_pos_of_pos hδ)
  rw [mul_inv_cancel₀ (ne_of_gt (sq_pos_of_pos hδ))] at hp
  change (3 / 4 : ℝ) ≤ δ ^ 2 * (⌊(δ ^ 2)⁻¹⌋₊ : ℝ)
  nlinarith

def boundedSurrogate (δ η : ℝ) : ℝ[X] :=
  surrogate δ (geometricOrder δ) (majorityOrder η)

/-- The exact intermediate construction, with no approximation hypotheses.
Its degree is deliberately not advertised as optimal. -/
theorem boundedSurrogate_spec {δ η : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hη : 0 < η) :
    Function.Even (boundedSurrogate δ η).eval ∧
    (∀ x : ℝ, |x| ≤ 1 → |(boundedSurrogate δ η).eval x| ≤ 1) ∧
    (∀ x : ℝ, δ ≤ |x| → |x| ≤ 1 →
      |(boundedSurrogate δ η).eval x - δ ^ 2 / (2 * x ^ 2)| ≤ η / 4) ∧
    (boundedSurrogate δ η).natDegree ≤
      2 * geometricOrder δ * (2 * majorityOrder η + 1) := by
  refine ⟨surrogate_even _ _ _, ?_, ?_, surrogate_degree _ _ _⟩
  · intro x hx
    change |(surrogate δ (geometricOrder δ) (majorityOrder η)).eval x| ≤ 1
    rw [abs_of_nonneg (surrogate_nonneg _ _ hx)]
    exact (surrogate_le _ _ hx).trans (geometricOrder_upper hδ)
  · intro x hx0 hx1
    exact (surrogate_error _ _ hδ (geometricOrder_lower hδ hδ1) hx0 hx1).trans
      (majorityOrder_tail hη)

end OptimalQLS.InverseSquare
