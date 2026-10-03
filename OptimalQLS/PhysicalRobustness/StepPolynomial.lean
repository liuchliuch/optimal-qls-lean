import OptimalQLS.InverseSquare.Accuracy

/-! An explicit bounded even high-pass polynomial with logarithmic degree.
This acts on a constant-gap encoding; its construction uses the previously
proved binomial-majority polynomials, with no approximation certificate. -/
noncomputable section
namespace OptimalQLS.PhysicalRobustness
open Polynomial InverseSquare

/-- Fixed-degree amplification of a nonnegative constant-gap signal. -/
def stepArgument : ℝ[X] := 1-(1-X^2)^10

def stepPolynomial (η : ℝ) : ℝ[X] :=
  (majority (majorityOrder (2*η))).comp stepArgument

@[simp] theorem stepArgument_eval (x : ℝ) : stepArgument.eval x = 1-(1-x^2)^10 := by
  simp [stepArgument]

@[simp] theorem stepPolynomial_eval (η x : ℝ) :
    (stepPolynomial η).eval x =
      (majority (majorityOrder (2*η))).eval (1-(1-x^2)^10) := by
  simp [stepPolynomial]

theorem stepArgument_interval {x : ℝ} (hx : |x| ≤ 1) :
    0 ≤ stepArgument.eval x ∧ stepArgument.eval x ≤ 1 := by
  have hs : 0 ≤ 1-x^2 := by nlinarith [sq_abs x, abs_nonneg x]
  have hu : 1-x^2 ≤ 1 := by nlinarith [sq_nonneg x]
  rw [stepArgument_eval]
  exact ⟨sub_nonneg.mpr (pow_le_one₀ hs hu), by linarith [pow_nonneg hs 10]⟩

theorem stepArgument_low {x : ℝ} (hx : |x| ≤ 1/8) :
    stepArgument.eval x ≤ 32/65 := by
  have hs : (63/64 : ℝ) ≤ 1-x^2 := by nlinarith [sq_abs x, abs_nonneg x]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 63/64) hs 10
  rw [stepArgument_eval]
  norm_num at hp ⊢
  linarith

theorem stepArgument_high {x : ℝ} (hx0 : 1/3 ≤ |x|) (hx1 : |x| ≤ 1) :
    33/65 ≤ stepArgument.eval x := by
  have hs : 0 ≤ 1-x^2 := by nlinarith [sq_abs x, abs_nonneg x]
  have hu : 1-x^2 ≤ (8/9 : ℝ) := by nlinarith [sq_abs x, abs_nonneg x]
  have hp := pow_le_pow_left₀ hs hu 10
  rw [stepArgument_eval]
  norm_num at hp ⊢
  linarith

theorem stepPolynomial_even (η : ℝ) : Function.Even (stepPolynomial η).eval := by
  intro x
  simp only [stepPolynomial_eval, neg_sq]

theorem stepPolynomial_interval (η : ℝ) {x : ℝ} (hx : |x| ≤ 1) :
    0 ≤ (stepPolynomial η).eval x ∧ (stepPolynomial η).eval x ≤ 1 := by
  have h := stepArgument_interval hx
  rw [stepPolynomial, eval_comp]
  exact ⟨majority_nonneg _ h.1 h.2, majority_le_one _ h.1 h.2⟩

theorem stepPolynomial_tail {η : ℝ} (hη : 0 < η) :
    (4224/4225 : ℝ)^majorityOrder (2*η) ≤ η := by
  have h := majorityOrder_tail (η := 2*η) (by positivity)
  nlinarith

/-- Low-spectrum suppression with absolute error η. -/
theorem stepPolynomial_low {η x : ℝ} (hη : 0 < η) (hx : |x| ≤ 1/8) :
    |(stepPolynomial η).eval x| ≤ η := by
  have hx1 : |x| ≤ 1 := by linarith
  have hs := stepArgument_interval hx1
  have hl := stepArgument_low hx
  have hc := majority_complement (majorityOrder (2*η)) (stepArgument.eval x)
  have hf := majority_failure_fixed (majorityOrder (2*η))
    (by linarith : (33/65 : ℝ) ≤ 1-stepArgument.eval x) (by linarith : 1-stepArgument.eval x ≤ 1)
  rw [abs_of_nonneg (stepPolynomial_interval η hx1).1]
  rw [stepPolynomial, eval_comp]
  linarith [stepPolynomial_tail hη]

/-- High-spectrum retention with absolute error η. -/
theorem stepPolynomial_high {η x : ℝ} (hη : 0 < η)
    (hx0 : 1/3 ≤ |x|) (hx1 : |x| ≤ 1) :
    |(stepPolynomial η).eval x-1| ≤ η := by
  have hs := stepArgument_interval hx1
  have hh := stepArgument_high hx0 hx1
  have hf := majority_failure_fixed (majorityOrder (2*η)) hh hs.2
  rw [abs_of_nonpos (by linarith [(stepPolynomial_interval η hx1).2] :
    (stepPolynomial η).eval x-1 ≤ 0)]
  rw [stepPolynomial, eval_comp]
  linarith [stepPolynomial_tail hη]

theorem stepPolynomial_degree (η : ℝ) :
    (stepPolynomial η).natDegree ≤ 20*(2*majorityOrder (2*η)+1) := by
  have hm (k : ℕ) : (majority k).natDegree ≤ 2*k+1 := by
    rw [majority_factor]
    exact natDegree_mul_le.trans (by
      have h := majorityQuotient_degree k
      rw [natDegree_X]
      omega)
  have hbase : (1-(X : ℝ[X])^2).natDegree ≤ 2 :=
    (natDegree_sub_le _ _).trans (max_le (by simp) (by simp))
  have ha : stepArgument.natDegree ≤ 20 := by
    unfold stepArgument
    exact (natDegree_sub_le _ _).trans (max_le (by simp)
      ((natDegree_pow_le).trans (by nlinarith)))
  unfold stepPolynomial
  exact natDegree_comp_le.trans (by nlinarith [Nat.mul_le_mul (hm (majorityOrder (2*η))) ha])

/-- Explicit uniform degree constant for the fixed-gap step. -/
theorem stepPolynomial_degree_complexity {η : ℝ} (hη : 0 < η) (hη1 : η < 1/2) :
    ((stepPolynomial η).natDegree : ℝ) ≤ 170000*Real.log (1/η) := by
  have htwo : (2:ℝ) ≤ 1/η := (le_div_iff₀ hη).mpr (by linarith)
  have hlogtwo : (1/2:ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    exact h
  have hL : (1/2:ℝ) ≤ Real.log (1/η) :=
    hlogtwo.trans (Real.log_le_log (by norm_num) htwo)
  have heq : (2:ℝ)/(2*η)=1/η := by ring
  have hn := Nat.ceil_lt_add_one (show 0 ≤ 4225*Real.log (2/(2*η)) by rw [heq]; positivity)
  change (majorityOrder (2*η) : ℝ) < 4225*Real.log (2/(2*η))+1 at hn
  rw [heq] at hn
  have hd : ((stepPolynomial η).natDegree : ℝ) ≤ 20*(2*(majorityOrder (2*η) : ℝ)+1) :=
    by exact_mod_cast stepPolynomial_degree η
  nlinarith

end OptimalQLS.PhysicalRobustness
