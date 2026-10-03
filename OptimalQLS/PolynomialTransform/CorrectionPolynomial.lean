import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Algebraic correction-polynomial transformation

The inverse-square approximation is kept as explicit scalar hypotheses in
this file. These results do not assert the existence or circuit realization
of that approximating polynomial.
-/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Polynomial

/-- The exact correction-polynomial formula in Lemma 5.4. -/
def correctionPolynomial (p : ℝ[X]) : ℝ[X] := C (1 / 4) * (1 + C 2 * p)

@[simp] theorem correctionPolynomial_eval (p : ℝ[X]) (x : ℝ) :
    (correctionPolynomial p).eval x = (1 + 2 * p.eval x) / 4 := by
  simp [correctionPolynomial]
  ring

theorem correctionPolynomial_even {p : ℝ[X]} (hp : Function.Even p.eval) :
    Function.Even (correctionPolynomial p).eval := by
  intro x
  simp only [correctionPolynomial_eval, hp x]

theorem correctionPolynomial_degree (p : ℝ[X]) :
    (correctionPolynomial p).natDegree ≤ p.natDegree := by
  apply (natDegree_C_mul_le _ _).trans
  exact natDegree_add_le_of_degree_le (by simp) (natDegree_C_mul_le _ _)

/-- The correction polynomial has slack 1/4 below the QSVT bound. -/
theorem correctionPolynomial_bounded {p : ℝ[X]} {x : ℝ} (hp : |p.eval x| ≤ 1) :
    |(correctionPolynomial p).eval x| ≤ 3 / 4 := by
  rw [correctionPolynomial_eval, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4)).mpr
  calc
    |1 + 2 * p.eval x| ≤ |(1 : ℝ)| + |2 * p.eval x| := abs_add_le _ _
    _ ≤ 3 := by rw [abs_mul]; norm_num; linarith

/-- The scalar approximation error is divided by exactly two. -/
theorem correctionPolynomial_error {p : ℝ[X]} {δ η x : ℝ}
    (hp : |p.eval x - δ ^ 2 / (2 * x ^ 2)| ≤ η) :
    |(correctionPolynomial p).eval x - (1 + δ ^ 2 / x ^ 2) / 4| ≤ η / 2 := by
  have heq : (correctionPolynomial p).eval x - (1 + δ ^ 2 / x ^ 2) / 4 =
      (p.eval x - δ ^ 2 / (2 * x ^ 2)) / 2 := by
    rw [correctionPolynomial_eval]
    ring
  rw [heq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact div_le_div_of_nonneg_right hp (by norm_num)

/-- Algebraic/scalar content of Lemma 5.4, parameterized only by the
explicit inverse-square approximation premises required from Lemma 2.5. -/
theorem lemma54_from_inverse_square (p : ℝ[X]) {κ η : ℝ}
    (heven : Function.Even p.eval)
    (hbounded : ∀ x : ℝ, |x| ≤ 1 → |p.eval x| ≤ 1)
    (happrox : ∀ x : ℝ, κ⁻¹ ≤ |x| → |x| ≤ 1 →
      |p.eval x - (κ⁻¹) ^ 2 / (2 * x ^ 2)| ≤ η) :
    Function.Even (correctionPolynomial p).eval ∧
    (correctionPolynomial p).natDegree ≤ p.natDegree ∧
    (∀ x : ℝ, |x| ≤ 1 → |(correctionPolynomial p).eval x| ≤ 3 / 4) ∧
    (∀ x : ℝ, κ⁻¹ ≤ |x| → |x| ≤ 1 →
      |(correctionPolynomial p).eval x - (1 + (κ⁻¹)^2 / x^2) / 4| ≤ η / 2) := by
  exact ⟨correctionPolynomial_even heven, correctionPolynomial_degree p,
    fun x hx => correctionPolynomial_bounded (hbounded x hx),
    fun x hx0 hx1 => correctionPolynomial_error (happrox x hx0 hx1)⟩

end OptimalQLS.PolynomialTransform
