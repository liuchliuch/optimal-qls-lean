import OptimalQLS.InverseSquare.Expansion
import OptimalQLS.InverseSquare.WeightedCompression

/-!
# Constructive optimal inverse-square approximation

All approximation inputs below are proved from concrete finite polynomial
sums. The degree-reduction step is an explicit Chebyshev truncation.
-/
noncomputable section
namespace OptimalQLS.InverseSquare
open Polynomial Finset

def reciprocalCeiling (δ : ℝ) : ℕ := ⌈δ⁻¹⌉₊

def compressionOrder (δ η : ℝ) : ℕ :=
  4 * (2 * majorityOrder η + 1) * reciprocalCeiling δ

def rawInverseSquare (δ η : ℝ) : ℝ[X] :=
  weightedCompression (expansionIndices (geometricOrder δ) (majorityOrder η))
    (expansionCoefficient δ (majorityOrder η)) (expansionExponent (geometricOrder δ))
    (compressionOrder δ η)

/-- Final normalization restores the exact QSVT bound one. -/
def inverseSquarePolynomial (δ η : ℝ) : ℝ[X] :=
  C ((1 + η)⁻¹) * rawInverseSquare δ η

theorem reciprocalCeiling_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < reciprocalCeiling δ := by
  have h := Nat.le_ceil (δ⁻¹)
  have hp : 0 < (reciprocalCeiling δ : ℝ) := lt_of_lt_of_le (inv_pos.mpr hδ) h
  exact_mod_cast hp

theorem geometricOrder_le_ceiling_sq {δ : ℝ} (hδ : 0 < δ) :
    geometricOrder δ ≤ (reciprocalCeiling δ) ^ 2 := by
  have hf : (geometricOrder δ : ℝ) ≤ (δ ^ 2)⁻¹ :=
    Nat.floor_le (show 0 ≤ (δ ^ 2)⁻¹ by positivity)
  have hc : δ⁻¹ ≤ (reciprocalCeiling δ : ℝ) := Nat.le_ceil _
  have hc0 : 0 ≤ δ⁻¹ := by positivity
  rw [← inv_pow] at hf
  have hh : (geometricOrder δ : ℝ) ≤ (reciprocalCeiling δ : ℝ) ^ 2 := by
    nlinarith
  exact_mod_cast hh

/-- Uniform choice of the moment parameter handles every power in the expansion. -/
theorem compression_exponent_bound {M K : ℕ} (k : ℕ)
    (hK : 0 < K) (hM : M ≤ K ^ 2) :
    ((M * (2 * k + 1) : ℕ) : ℝ) * (2 / (K : ℝ)) ^ 2 / 4 -
        (2 / (K : ℝ)) * ((4 * (2 * k + 1) * K : ℕ) : ℝ) ≤
      -7 * (2 * k + 1 : ℝ) := by
  have hKr : 0 < (K : ℝ) := by exact_mod_cast hK
  have hMr : (M : ℝ) ≤ (K : ℝ) ^ 2 := by exact_mod_cast hM
  have hd : (M : ℝ) / (K : ℝ) ^ 2 ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos hKr)).mpr
    exact hMr
  have heq : ((M * (2 * k + 1) : ℕ) : ℝ) * (2 / (K : ℝ)) ^ 2 / 4 -
      (2 / (K : ℝ)) * ((4 * (2 * k + 1) * K : ℕ) : ℝ) =
      ((M : ℝ) / (K : ℝ) ^ 2) * (2 * k + 1) - 8 * (2 * k + 1) := by
    push_cast
    field_simp
    ring
  rw [heq]
  have hh := mul_le_mul_of_nonneg_right hd (show (0 : ℝ) ≤ 2 * k + 1 by positivity)
  nlinarith

/-- The expansion weight is absorbed into the exponential truncation error. -/
theorem compression_weight_exponential (k : ℕ) :
    (3 : ℝ) ^ (2 * k + 1) * (2 * Real.exp (-7 * (2 * k + 1 : ℝ))) ≤
      2 * Real.exp (-5 * (2 * k + 1 : ℝ)) := by
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) h3 (2 * k + 1)
  rw [← Real.exp_nat_mul] at hp
  calc
    _ ≤ Real.exp (((2 * k + 1 : ℕ) : ℝ) * 2) *
        (2 * Real.exp (-7 * (2 * k + 1 : ℝ))) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by
      rw [show Real.exp (((2 * k + 1 : ℕ) : ℝ) * 2) *
        (2 * Real.exp (-7 * (2 * k + 1 : ℝ))) =
        2 * (Real.exp (((2 * k + 1 : ℕ) : ℝ) * 2) *
          Real.exp (-7 * (2 * k + 1 : ℝ))) by ring, ← Real.exp_add]
      congr 2
      push_cast
      ring

theorem compression_accuracy_tail {η : ℝ} (hη : 0 < η) :
    2 * Real.exp (-5 * (2 * majorityOrder η + 1 : ℝ)) ≤ η / 4 := by
  have ho : 4225 * Real.log (2 / η) ≤ (majorityOrder η : ℝ) := Nat.le_ceil _
  have he : Real.exp (-((majorityOrder η : ℝ) / 4225)) ≤ η / 2 := by
    have hh : -((majorityOrder η : ℝ) / 4225) ≤ -Real.log (2 / η) := by linarith
    apply (Real.exp_le_exp.mpr hh).trans
    rw [Real.exp_neg, Real.exp_log (div_pos (by norm_num) hη)]
    apply le_of_eq
    field_simp
  have h3 : Real.exp (-3 : ℝ) ≤ (1 / 4 : ℝ) := by
    have hp : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp 3]
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) hp
  have hh : -5 * (2 * majorityOrder η + 1 : ℝ) ≤
      -3 + -((majorityOrder η : ℝ) / 4225) := by
    have hp : (0 : ℝ) ≤ majorityOrder η := by positivity
    linarith
  have hexp := Real.exp_le_exp.mpr hh
  rw [Real.exp_add] at hexp
  have hmul := mul_le_mul h3 he (le_of_lt (Real.exp_pos _)) (by norm_num : (0 : ℝ) ≤ 1 / 4)
  nlinarith

/-- Compression of the explicit bounded surrogate, with a proved error budget. -/
theorem rawInverseSquare_close {δ η x : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hx : |x| ≤ 1) :
    |(rawInverseSquare δ η).eval x - (boundedSurrogate δ η).eval x| ≤ η / 4 := by
  unfold rawInverseSquare boundedSurrogate
  rw [surrogate_expansion]
  have hK := reciprocalCeiling_pos hδ
  have ht : 0 ≤ 2 / (reciprocalCeiling δ : ℝ) := by positivity
  have h := weightedCompression_error
    (expansionIndices (geometricOrder δ) (majorityOrder η))
    (expansionCoefficient δ (majorityOrder η))
    (expansionExponent (geometricOrder δ)) (compressionOrder δ η)
    (geometricOrder δ * (2 * majorityOrder η + 1))
    (fun _ ha => expansionExponent_le ha)
    (expansionWeight_bound (majorityOrder η) (geometricOrder_upper hδ)) ht hx
  apply h.trans
  have he := compression_exponent_bound (majorityOrder η) hK (geometricOrder_le_ceiling_sq hδ)
  calc
    _ ≤ (3 : ℝ) ^ (2 * majorityOrder η + 1) *
        (2 * Real.exp (-7 * (2 * majorityOrder η + 1 : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.exp_le_exp.mpr he
    _ ≤ 2 * Real.exp (-5 * (2 * majorityOrder η + 1 : ℝ)) := compression_weight_exponential _
    _ ≤ η / 4 := compression_accuracy_tail hη

theorem inverseSquarePolynomial_even (δ η : ℝ) :
    Function.Even (inverseSquarePolynomial δ η).eval := by
  intro x
  simp only [inverseSquarePolynomial, eval_mul, eval_C]
  congr 1
  exact weightedCompression_even _ _ _ _ x

theorem inverseSquarePolynomial_degree_nat (δ η : ℝ) :
    (inverseSquarePolynomial δ η).natDegree ≤ 2 * compressionOrder δ η := by
  unfold inverseSquarePolynomial rawInverseSquare
  exact (natDegree_C_mul_le _ _).trans (weightedCompression_degree _ _ _ _)

theorem inverseSquarePolynomial_bounded {δ η x : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hη : 0 < η) (hx : |x| ≤ 1) :
    |(inverseSquarePolynomial δ η).eval x| ≤ 1 := by
  have hs := (boundedSurrogate_spec hδ hδ1 hη).2.1 x hx
  have hc := rawInverseSquare_close hδ hη hx
  have hraw : |(rawInverseSquare δ η).eval x| ≤ 1 + η / 4 := by
    have h := abs_add_le ((rawInverseSquare δ η).eval x - (boundedSurrogate δ η).eval x)
      ((boundedSurrogate δ η).eval x)
    rw [sub_add_cancel] at h
    linarith
  have hy : 0 < 1 + η := by linarith
  have hd : |(rawInverseSquare δ η).eval x| / (1 + η) ≤ 1 :=
    (div_le_one hy).mpr (by linarith)
  simpa only [inverseSquarePolynomial, eval_mul, eval_C, abs_mul, abs_inv,
    abs_of_pos hy, div_eq_mul_inv, mul_comm] using hd

theorem inverseSquarePolynomial_error {δ η x : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hη : 0 < η)
    (hx0 : δ ≤ |x|) (hx1 : |x| ≤ 1) :
    |(inverseSquarePolynomial δ η).eval x - δ ^ 2 / (2 * x ^ 2)| ≤ η := by
  have hs := (boundedSurrogate_spec hδ hδ1 hη).2.2.1 x hx0 hx1
  have hc := rawInverseSquare_close hδ hη hx1
  have hraw : |(rawInverseSquare δ η).eval x - δ ^ 2 / (2 * x ^ 2)| ≤ η / 2 := by
    have h := abs_add_le ((rawInverseSquare δ η).eval x - (boundedSurrogate δ η).eval x)
      ((boundedSurrogate δ η).eval x - δ ^ 2 / (2 * x ^ 2))
    have heq : (rawInverseSquare δ η).eval x - (boundedSurrogate δ η).eval x +
        ((boundedSurrogate δ η).eval x - δ ^ 2 / (2 * x ^ 2)) =
        (rawInverseSquare δ η).eval x - δ ^ 2 / (2 * x ^ 2) := by ring
    rw [heq] at h
    linarith
  have hxne : x ≠ 0 := abs_pos.mp (lt_of_lt_of_le hδ hx0)
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hxne
  have hf0 : 0 ≤ δ ^ 2 / (2 * x ^ 2) := by positivity
  have hf1 : δ ^ 2 / (2 * x ^ 2) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * x ^ 2)).mpr
    nlinarith [sq_abs x, abs_nonneg x]
  have hy : 0 < 1 + η := by linarith
  have heq : (inverseSquarePolynomial δ η).eval x - δ ^ 2 / (2 * x ^ 2) =
      ((rawInverseSquare δ η).eval x - δ ^ 2 / (2 * x ^ 2) -
        η * (δ ^ 2 / (2 * x ^ 2))) / (1 + η) := by
    simp only [inverseSquarePolynomial, eval_mul, eval_C]
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hy]
  apply (div_le_iff₀ hy).mpr
  have habs := abs_sub ((rawInverseSquare δ η).eval x - δ ^ 2 / (2 * x ^ 2))
    (η * (δ ^ 2 / (2 * x ^ 2)))
  rw [abs_of_nonneg (mul_nonneg hη.le hf0)] at habs
  have hm := mul_le_mul_of_nonneg_left hf1 hη.le
  nlinarith

/-- An explicit universal constant witnesses the optimal asymptotic degree. -/
theorem inverseSquarePolynomial_degree {δ η : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hη : 0 < η) (hη1 : η < 1 / 2) :
    ((inverseSquarePolynomial δ η).natDegree : ℝ) ≤
      210000 * δ⁻¹ * Real.log (1 / η) := by
  have htwo : (2 : ℝ) ≤ 1 / η := (le_div_iff₀ hη).mpr (by linarith)
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hL : (1 / 2 : ℝ) ≤ Real.log (1 / η) :=
    hlogtwo.trans (Real.log_le_log (by norm_num) htwo)
  have hlog : Real.log (2 / η) ≤ 2 * Real.log (1 / η) := by
    have he : Real.log (2 / η) = Real.log 2 + Real.log (1 / η) := by
      rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hη.ne',
        Real.log_div one_ne_zero hη.ne', Real.log_one]
      ring
    rw [he]
    linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) htwo]
  have hlog0 : 0 ≤ Real.log (2 / η) := Real.log_nonneg (by
    apply (le_div_iff₀ hη).mpr
    linarith)
  have hk : (majorityOrder η : ℝ) ≤ 8450 * Real.log (1 / η) + 1 := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 4225 * Real.log (2 / η) by positivity)
    change (majorityOrder η : ℝ) < 4225 * Real.log (2 / η) + 1 at hh
    linarith
  have hn : (2 * majorityOrder η + 1 : ℝ) ≤ 16906 * Real.log (1 / η) := by
    linarith
  have hκ : (2 : ℝ) ≤ δ⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hδ).mpr (by linarith)
  have hK : (reciprocalCeiling δ : ℝ) ≤ (3 / 2 : ℝ) * δ⁻¹ := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ δ⁻¹ by positivity)
    change (reciprocalCeiling δ : ℝ) < δ⁻¹ + 1 at hh
    linarith
  have hdeg : ((inverseSquarePolynomial δ η).natDegree : ℝ) ≤
      8 * (2 * majorityOrder η + 1 : ℝ) * reciprocalCeiling δ := by
    have hh := inverseSquarePolynomial_degree_nat δ η
    unfold compressionOrder at hh
    have heq : 2 * (4 * (2 * majorityOrder η + 1) * reciprocalCeiling δ) =
        8 * (2 * majorityOrder η + 1) * reciprocalCeiling δ := by ring
    rw [heq] at hh
    exact_mod_cast hh
  calc
    _ ≤ 8 * (2 * majorityOrder η + 1 : ℝ) * reciprocalCeiling δ := hdeg
    _ ≤ 8 * (16906 * Real.log (1 / η)) * ((3 / 2 : ℝ) * δ⁻¹) := by
      apply mul_le_mul _ hK (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hn (by norm_num)
    _ ≤ 210000 * δ⁻¹ * Real.log (1 / η) := by
      have hp : 0 ≤ δ⁻¹ * Real.log (1 / η) := by positivity
      nlinarith

/-- Paper Lemma 2.5: an actual even polynomial, globally bounded and optimally
approximating the normalized inverse square on both spectral intervals. -/
theorem lemma25_inverse_square {δ η : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hη : 0 < η) (hη1 : η < 1 / 2) :
    ∃ p : ℝ[X], Function.Even p.eval ∧
      (∀ x : ℝ, |x| ≤ 1 → |p.eval x| ≤ 1) ∧
      (∀ x : ℝ, δ ≤ |x| → |x| ≤ 1 → |p.eval x - δ ^ 2 / (2 * x ^ 2)| ≤ η) ∧
      (p.natDegree : ℝ) ≤ 210000 * δ⁻¹ * Real.log (1 / η) := by
  exact ⟨inverseSquarePolynomial δ η, inverseSquarePolynomial_even δ η,
    fun _ hx => inverseSquarePolynomial_bounded hδ hδ1 hη hx,
    fun _ hx0 hx1 => inverseSquarePolynomial_error hδ hδ1 hη hx0 hx1,
    inverseSquarePolynomial_degree hδ hδ1 hη hη1⟩

/-- Condition-number form of Lemma 2.5 for the paper's correction-polynomial input. -/
theorem lemma25_inverse_square_kappa {κ η : ℝ}
    (hκ : 2 ≤ κ) (hη : 0 < η) (hη1 : η < 1 / 2) :
    ∃ p : ℝ[X], Function.Even p.eval ∧
      (∀ x : ℝ, |x| ≤ 1 → |p.eval x| ≤ 1) ∧
      (∀ x : ℝ, κ⁻¹ ≤ |x| → |x| ≤ 1 →
        |p.eval x - (κ⁻¹) ^ 2 / (2 * x ^ 2)| ≤ η) ∧
      (p.natDegree : ℝ) ≤ 210000 * κ * Real.log (1 / η) := by
  have hκ0 : 0 < κ := by linarith
  have hδ0 : 0 < κ⁻¹ := inv_pos.mpr hκ0
  have hδ1 : κ⁻¹ ≤ (1 / 2 : ℝ) := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hκ
  simpa only [inv_inv] using lemma25_inverse_square hδ0 hδ1 hη hη1

end OptimalQLS.InverseSquare
