import OptimalQLS.PhysicalRobustness.StepPolynomial
import OptimalQLS.PolynomialTransform.GraphFilter
import Mathlib.Algebra.Polynomial.Inductions

/-! A literal O(κ)-degree regularizer polynomial, obtained algebraically from
an existing constant-precision Chebyshev graph filter. It avoids nested oracle
encodings and every per-query active-data comparison. -/
noncomputable section
namespace OptimalQLS.PhysicalRobustness
open Polynomial Polynomial.Chebyshev PolynomialTransform

/-- The even graph filter expressed in the squared, unnormalized variable. -/
def squareGraphFilter (κ : ℝ) : ℝ[X] :=
  C (((T ℝ (filterOrder (graphFilterGap κ) (1/1024) : ℤ)).eval
      (-filterEndpoint (graphFilterGap κ)))⁻¹) *
    (T ℝ (filterOrder (graphFilterGap κ) (1/1024) : ℤ)).comp
      (-1+C (2/(1-(graphFilterGap κ)^2)) *
        (C (((1+κ⁻¹)⁻¹)^2)*X-C ((graphFilterGap κ)^2)))

/-- Half the regularized high-pass function, made polynomial by exact division
by X before substituting `X²+κ⁻²`. -/
def regularizerPolynomial (κ : ℝ) : ℝ[X] :=
  C (1/2)*X^2*(divX (1-squareGraphFilter κ)).comp (X^2+C ((κ⁻¹)^2))

@[simp] theorem squareGraphFilter_eval (κ y : ℝ) :
    (squareGraphFilter κ).eval y =
      (T ℝ (filterOrder (graphFilterGap κ) (1/1024) : ℤ)).eval
        (-1+2*(((1+κ⁻¹)⁻¹)^2*y-(graphFilterGap κ)^2)/(1-(graphFilterGap κ)^2)) /
      (T ℝ (filterOrder (graphFilterGap κ) (1/1024) : ℤ)).eval
        (-filterEndpoint (graphFilterGap κ)) := by
  simp only [squareGraphFilter, eval_mul, eval_C, eval_comp, eval_add,
    eval_neg, eval_one, eval_sub, eval_X]
  have ha : 2/(1-(graphFilterGap κ)^2)*(((1+κ⁻¹)⁻¹)^2*y-(graphFilterGap κ)^2) =
      2*(((1+κ⁻¹)⁻¹)^2*y-(graphFilterGap κ)^2)/(1-(graphFilterGap κ)^2) := by ring
  rw [ha]
  ring

/-- Literal relation to the pre-existing proved Chebyshev filter. -/
theorem squareGraphFilter_eval_sq (κ x : ℝ) :
    (squareGraphFilter κ).eval (x^2) =
      (kernelFilter (graphFilterGap κ) (1/1024)).eval (x/(1+κ⁻¹)) := by
  rw [squareGraphFilter_eval, kernelFilter, chebyshevFilter_eval]
  congr 2
  simp only [div_pow, inv_pow]
  ring

theorem squareGraphFilter_zero {κ : ℝ} (hκ : 0 < κ) :
    (squareGraphFilter κ).eval 0 = 1 := by
  have hg := graphFilterGap_pos hκ
  have hg1 : graphFilterGap κ ≤ 1/3 := filter_parameter_le_third (min_le_right _ _)
  have hgsq : (graphFilterGap κ)^2 < 1 := by nlinarith
  have hs := squareGraphFilter_eval_sq κ 0
  simpa [kernelFilter, chebyshevFilter_zero hgsq] using hs

/-- Exact quotient formula on all real data eigenvalues. -/
theorem regularizerPolynomial_eval {κ : ℝ} (hκ : 0 < κ) (x : ℝ) :
    (regularizerPolynomial κ).eval x =
      x^2*(1-(squareGraphFilter κ).eval (x^2+(κ⁻¹)^2))/(2*(x^2+(κ⁻¹)^2)) := by
  have hc : (1-squareGraphFilter κ).coeff 0 = 0 := by
    have hz : (squareGraphFilter κ).coeff 0 = 1 := by
      simpa only [Polynomial.coeff_zero_eq_eval_zero] using squareGraphFilter_zero hκ
    simp [hz]
  have hh := congrArg (fun p : ℝ[X] => p.eval (x^2+(κ⁻¹)^2))
    (X_mul_divX_add (1-squareGraphFilter κ))
  simp only [eval_add, eval_mul, eval_X, eval_C, hc, add_zero, eval_sub, eval_one] at hh
  have hd : x^2+(κ⁻¹)^2 ≠ 0 := ne_of_gt (by positivity : 0 < x^2+(κ⁻¹)^2)
  simp only [regularizerPolynomial, eval_mul, eval_C, eval_pow, eval_X, eval_comp,
    eval_add]
  have hv : (divX (1-squareGraphFilter κ)).eval (x^2+(κ⁻¹)^2) =
      (1-(squareGraphFilter κ).eval (x^2+(κ⁻¹)^2))/(x^2+(κ⁻¹)^2) :=
    (eq_div_iff hd).mpr (by nlinarith [hh])
  rw [hv]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Every nonzero auxiliary eigenvalue lies in the existing filter's tail
interval, even when the physical data eigenvalue is arbitrarily close to zero. -/
theorem squareGraphFilter_tail {κ x : ℝ} (hκ : 0 < κ) (hx : |x| ≤ 1) :
    |(squareGraphFilter κ).eval (x^2+(κ⁻¹)^2)| ≤ 1/1024 := by
  let t := κ⁻¹
  let u := Real.sqrt (x^2+t^2)
  have ht : 0 < t := inv_pos.mpr hκ
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have husq : u^2 = x^2+t^2 := Real.sq_sqrt (by positivity)
  have hut : t ≤ u := (sq_le_sq₀ ht.le hu).mp (by nlinarith [sq_nonneg x])
  have hupp : u ≤ 1+t := (sq_le_sq₀ hu (by positivity)).mp (by
    nlinarith [sq_abs x, abs_nonneg x])
  have hnorm : 0 < 1+t := by positivity
  rw [← husq, squareGraphFilter_eval_sq]
  apply kernelFilter_tail (graphFilterGap_pos hκ) (min_le_right _ _) (by norm_num)
  · rw [abs_of_nonneg (div_nonneg hu hnorm.le)]
    apply (min_le_left _ _).trans
    change 1/(κ*(1+t)) ≤ u/(1+t)
    have heq : 1/(κ*(1+t)) = t/(1+t) := by dsimp [t]; field_simp
    rw [heq]
    exact div_le_div_of_nonneg_right hut hnorm.le
  · rw [abs_of_nonneg (div_nonneg hu hnorm.le)]
    exact (div_le_one hnorm).mpr hupp

/-- Constant uniform approximation to the rational regularizer, including zero. -/
theorem regularizerPolynomial_error {κ x : ℝ} (hκ : 0 < κ) (hx : |x| ≤ 1) :
    |(regularizerPolynomial κ).eval x-x^2/(2*(x^2+(κ⁻¹)^2))| ≤ 1/2048 := by
  have hd : 0 < 2*(x^2+(κ⁻¹)^2) := by positivity
  have hcoef0 : 0 ≤ x^2/(2*(x^2+(κ⁻¹)^2)) := by positivity
  have hcoef1 : x^2/(2*(x^2+(κ⁻¹)^2)) ≤ 1/2 :=
    (div_le_iff₀ hd).mpr (by nlinarith [sq_nonneg (κ⁻¹)])
  have heq : (regularizerPolynomial κ).eval x-x^2/(2*(x^2+(κ⁻¹)^2)) =
      -(x^2/(2*(x^2+(κ⁻¹)^2)))*(squareGraphFilter κ).eval (x^2+(κ⁻¹)^2) := by
    rw [regularizerPolynomial_eval hκ]
    ring
  rw [heq, abs_mul, abs_neg, abs_of_nonneg hcoef0]
  have hm := mul_le_mul hcoef1 (squareGraphFilter_tail hκ hx) (abs_nonneg _) (by norm_num : (0:ℝ)≤1/2)
  norm_num at hm ⊢
  exact hm

/-- Uniform boundedness on the complete QSVT signal interval. -/
theorem regularizerPolynomial_bounded {κ x : ℝ} (hκ : 0 < κ) (hx : |x| ≤ 1) :
    |(regularizerPolynomial κ).eval x| ≤ 1 := by
  have he := abs_le.mp (regularizerPolynomial_error hκ hx)
  have hd : 0 < 2*(x^2+(κ⁻¹)^2) := by positivity
  have hc0 : 0 ≤ x^2/(2*(x^2+(κ⁻¹)^2)) := by positivity
  have hc1 : x^2/(2*(x^2+(κ⁻¹)^2)) ≤ 1/2 :=
    (div_le_iff₀ hd).mpr (by nlinarith [sq_nonneg (κ⁻¹)])
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem regularizerPolynomial_even (κ : ℝ) : Function.Even (regularizerPolynomial κ).eval := by
  intro x
  simp only [regularizerPolynomial, eval_mul, eval_C, eval_pow, eval_X, eval_comp,
    eval_add, neg_sq]

/-- The low noisy cluster enters the fixed suppression interval. -/
theorem regularizerPolynomial_low {κ x : ℝ} (hκ : 0 < κ) (hx1 : |x| ≤ 1)
    (hx : |x| ≤ κ⁻¹/2) : |(regularizerPolynomial κ).eval x| ≤ 1/8 := by
  have he := abs_le.mp (regularizerPolynomial_error hκ hx1)
  have hd : 0 < 2*(x^2+(κ⁻¹)^2) := by positivity
  have hx2 : x^2 ≤ (κ⁻¹)^2/4 := by nlinarith [sq_abs x, abs_nonneg x]
  have hc0 : 0 ≤ x^2/(2*(x^2+(κ⁻¹)^2)) := by positivity
  have hc1 : x^2/(2*(x^2+(κ⁻¹)^2)) ≤ 1/10 :=
    (div_le_iff₀ hd).mpr (by nlinarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The high noisy cluster enters the fixed retention interval. -/
theorem regularizerPolynomial_high {κ x : ℝ} (hκ : 0 < κ) (hx1 : |x| ≤ 1)
    (hx : 3*κ⁻¹/2 ≤ |x|) : 1/3 ≤ |(regularizerPolynomial κ).eval x| := by
  have he := abs_le.mp (regularizerPolynomial_error hκ hx1)
  have hd : 0 < 2*(x^2+(κ⁻¹)^2) := by positivity
  have hx2 : 9*(κ⁻¹)^2/4 ≤ x^2 := by
    have hs := (sq_le_sq₀ (by positivity : 0 ≤ 3*κ⁻¹/2) (abs_nonneg x)).mpr hx
    rw [sq_abs] at hs
    nlinarith
  have hc : 9/26 ≤ x^2/(2*(x^2+(κ⁻¹)^2)) :=
    (le_div_iff₀ hd).mpr (by nlinarith)
  exact (by linarith : (1/3:ℝ) ≤ (regularizerPolynomial κ).eval x).trans (le_abs_self _)

/-- A literal even polynomial separating the complete noisy spectral clusters. -/
def noisyHighPass (κ η : ℝ) : ℝ[X] := (stepPolynomial η).comp (regularizerPolynomial (2*κ))

theorem noisyHighPass_even (κ η : ℝ) : Function.Even (noisyHighPass κ η).eval := by
  intro x
  simp only [noisyHighPass, eval_comp, regularizerPolynomial_even (2*κ) x]

theorem noisyHighPass_bounded {κ : ℝ} (hκ : 0 < κ) (η : ℝ) {x : ℝ} (hx : |x| ≤ 1) :
    |(noisyHighPass κ η).eval x| ≤ 1 := by
  have hq := regularizerPolynomial_bounded (κ := 2*κ) (by positivity) hx
  have hs := stepPolynomial_interval η hq
  rw [noisyHighPass, eval_comp, abs_of_nonneg hs.1]
  exact hs.2

/-- The base polynomial has degree linear in the graph-filter order. -/
theorem regularizerPolynomial_degree (κ : ℝ) :
    (regularizerPolynomial κ).natDegree ≤ 2*filterOrder (graphFilterGap κ) (1/1024)+2 := by
  let g := graphFilterGap κ
  let n := filterOrder g (1/1024)
  have hl : (-1+C (2/(1-g^2))*(C (((1+κ⁻¹)⁻¹)^2)*X-C (g^2)) : ℝ[X]).natDegree ≤ 1 := by
    apply (natDegree_add_le _ _).trans
    apply max_le (by simp)
    apply (natDegree_C_mul_le _ _).trans
    apply (natDegree_sub_le _ _).trans
    exact max_le ((natDegree_C_mul_le _ _).trans (by simp)) (by simp)
  have hw : (squareGraphFilter κ).natDegree ≤ n := by
    unfold squareGraphFilter
    apply (natDegree_C_mul_le _ _).trans
    apply natDegree_comp_le.trans
    have hT : (T ℝ (n : ℤ)).natDegree = n := by simp [natDegree_T]
    change (T ℝ (n : ℤ)).natDegree * _ ≤ n
    rw [hT]
    simpa using Nat.mul_le_mul_left n hl
  have hdiv : (divX (1-squareGraphFilter κ)).natDegree ≤ n :=
    natDegree_divX_le.trans ((natDegree_sub_le _ _).trans (max_le (by simp) hw))
  have hs : (X^2+C ((κ⁻¹)^2) : ℝ[X]).natDegree ≤ 2 :=
    (natDegree_add_le _ _).trans (max_le (by simp) (by simp))
  unfold regularizerPolynomial
  apply natDegree_mul_le.trans
  have hc : (C (1/2)*(X : ℝ[X])^2).natDegree ≤ 2 := (natDegree_C_mul_le _ _).trans (by simp)
  have hcomp := natDegree_comp_le (p := divX (1-squareGraphFilter κ)) (q := X^2+C ((κ⁻¹)^2))
  have hh := Nat.mul_le_mul hdiv hs
  change _ ≤ 2*n+2
  omega

/-- An explicit constant absorbs the fixed regularizer precision. -/
theorem regularizerPolynomial_degree_complexity {κ : ℝ} (hκ : 1 ≤ κ) :
    ((regularizerPolynomial κ).natDegree : ℝ) ≤ 25000*κ := by
  have hk : 0 < κ := by linarith
  have hg1 : graphFilterGap κ ≤ 1/3 := filter_parameter_le_third (min_le_right _ _)
  have hg : (graphFilterGap κ)^2 < 1 := by
    have hp := graphFilterGap_pos hk
    nlinarith
  have heq : (kernelFilter (graphFilterGap κ) (1/1024)).natDegree =
      2*filterOrder (graphFilterGap κ) (1/1024) := chebyshevFilter_natDegree hg _
  have hd : ((regularizerPolynomial κ).natDegree : ℝ) ≤
      (kernelFilter (graphFilterGap κ) (1/1024)).natDegree+2 := by
    exact_mod_cast (heq ▸ regularizerPolynomial_degree κ)
  have hf := graphFilter_degree_bound hκ (by norm_num : (0:ℝ)<1/1024) (by norm_num : (1/1024:ℝ)<1/2)
  have hlog : Real.log (1024:ℝ) ≤ 1024 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<1024)
    linarith
  norm_num only [one_div_div, div_one] at hf
  have hm := mul_le_mul_of_nonneg_left hlog (show 0≤24*κ by positivity)
  nlinarith

/-- The complete explicit high-pass transform has the desired degree. -/
theorem noisyHighPass_degree {κ η : ℝ} (hκ : 1 ≤ κ) (hη : 0 < η) (hη1 : η < 1/2) :
    ((noisyHighPass κ η).natDegree : ℝ) ≤ 8500000000*κ*Real.log (1/η) := by
  have hr := regularizerPolynomial_degree_complexity (κ := 2*κ) (by linarith)
  have hs := stepPolynomial_degree_complexity hη hη1
  have hc : ((noisyHighPass κ η).natDegree : ℝ) ≤
      (stepPolynomial η).natDegree*(regularizerPolynomial (2*κ)).natDegree := by
    exact_mod_cast (natDegree_comp_le (p := stepPolynomial η) (q := regularizerPolynomial (2*κ)))
  have hlog : 0≤Real.log (1/η) := Real.log_nonneg ((le_div_iff₀ hη).mpr (by linarith))
  have hm := mul_le_mul hs hr (by positivity : (0:ℝ)≤(regularizerPolynomial (2*κ)).natDegree)
    (by positivity : 0≤170000*Real.log (1/η))
  nlinarith

end OptimalQLS.PhysicalRobustness
