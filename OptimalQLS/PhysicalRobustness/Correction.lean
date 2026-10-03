import OptimalQLS.PhysicalRobustness.HighPass
import OptimalQLS.Refinement.CorrectionIdentity

/-! Actual bounded polynomial correction restricted to the noisy high spectrum. -/
noncomputable section
namespace OptimalQLS.PhysicalRobustness
open Polynomial Geometry PolynomialTransform Matrix
open scoped Matrix.Norms.L2Operator

def noisyCorrectionPolynomial (κ η : ℝ) : ℝ[X] :=
  noisyHighPass κ η * paperCorrectionPolynomial (2*κ) η

theorem noisyCorrectionPolynomial_even {κ η : ℝ} (hκ : 2≤κ) (hη : 0<η) (hη1 : η<1/2) :
    Function.Even (noisyCorrectionPolynomial κ η).eval := by
  have hp := (lemma54_correction_polynomial (κ := 2*κ) (by linarith) hη hη1).1
  intro x
  simp only [noisyCorrectionPolynomial,eval_mul,noisyHighPass_even κ η x,hp x]

theorem noisyCorrectionPolynomial_bounded {κ η x : ℝ}
    (hκ : 2≤κ) (hη : 0<η) (hη1 : η<1/2) (hx : |x|≤1) :
    |(noisyCorrectionPolynomial κ η).eval x|≤3/4 := by
  have hp := (lemma54_correction_polynomial (κ := 2*κ) (by linarith) hη hη1).2.1 x hx
  have hq := noisyHighPass_bounded (by linarith : 0<κ) η hx
  rw [noisyCorrectionPolynomial,eval_mul,abs_mul]
  exact (mul_le_mul hq hp (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- Scalar target is zero on the actual low cluster and the bounded inverse
correction on the high cluster; ordinary inverse at zero is never used. -/
def highCorrectionValue (κ δ x : ℝ) : ℝ :=
  if |x|≤δ then 0 else (1+((2*κ)⁻¹)^2/x^2)/4

theorem noisyCorrectionPolynomial_error {κ δ η x : ℝ}
    (hκ : 2≤κ) (hδ : 0≤δ) (hsmall : κ*δ≤1/4) (hη : 0<η) (hη1 : η<1/2)
    (hx : |x|≤1) (hgap : |x|≤δ ∨ κ⁻¹-δ≤|x|) :
    |(noisyCorrectionPolynomial κ η).eval x-highCorrectionValue κ δ x|≤5*η/4 := by
  have hk : 0<κ := by linarith
  have hc := lemma54_correction_polynomial (κ := 2*κ) (by linarith) hη hη1
  have hb := hc.2.1 x hx
  have hs := noisyHighPass_scalar hk hδ hsmall hη hx
  by_cases hl : |x|≤δ
  · simp only [highCorrectionValue,hl,if_true,sub_zero,noisyCorrectionPolynomial,eval_mul,abs_mul]
    have hm := mul_le_mul (hs.1 hl) hb (abs_nonneg _) hη.le
    nlinarith
  · have hxhigh := hgap.resolve_left hl
    have hi : (2*κ)⁻¹=κ⁻¹/2 := by field_simp
    have hd : δ≤κ⁻¹/4 := by
      rw [inv_eq_one_div,div_div]
      exact (le_div_iff₀ (by positivity : (0:ℝ)<κ*4)).mpr (by nlinarith)
    have hxk : (2*κ)⁻¹≤|x| := by rw [hi]; nlinarith [inv_pos.mpr hk]
    have he := hc.2.2.1 x hxk hx
    have hq := hs.2 hxhigh
    have hid : (noisyCorrectionPolynomial κ η).eval x-highCorrectionValue κ δ x =
        ((noisyHighPass κ η).eval x-1)*(paperCorrectionPolynomial (2*κ) η).eval x+
          ((paperCorrectionPolynomial (2*κ) η).eval x-(1+((2*κ)⁻¹)^2/x^2)/4) := by
      simp only [noisyCorrectionPolynomial,eval_mul,highCorrectionValue,hl,if_false]
      ring
    rw [hid]
    apply (abs_add_le _ _).trans
    rw [abs_mul]
    have hm := mul_le_mul hq hb (abs_nonneg _) hη.le
    nlinarith

section Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Canonical high-spectral ideal correction of the actual noisy operator. -/
def highCorrection (B : E →L[ℂ] E) (hB : B.toLinearMap.IsSymmetric) (κ δ : ℝ) : E →L[ℂ] E :=
  conjugate (hB.eigenvectorBasis rfl).repr
    (Geometry.diagonal (fun i => (highCorrectionValue κ δ (hB.eigenvalues rfl i) : ℂ)))

theorem noisyCorrection_operator_error (B : E →L[ℂ] E) (hB : B.toLinearMap.IsSymmetric)
    (hBn : ‖B‖≤1) {κ δ η : ℝ} (hκ : 2≤κ) (hδ : 0≤δ) (hsmall : κ*δ≤1/4)
    (hη : 0<η) (hη1 : η<1/2)
    (hgap : ∀ i, |hB.eigenvalues rfl i|≤δ ∨ κ⁻¹-δ≤|hB.eigenvalues rfl i|) :
    ‖polynomialOperator (noisyCorrectionPolynomial κ η) B-highCorrection B hB κ δ‖≤5*η/4 := by
  let U := (hB.eigenvectorBasis rfl).repr
  let a := hB.eigenvalues rfl
  have hd : ∀ x i, U (B x) i=(a i : ℂ)*U x i :=
    fun x i => hB.eigenvectorBasis_apply_self_apply rfl x i
  apply polynomial_diagonal_distance U B a hd _ _ (by positivity)
  intro i
  have ha : |a i|≤1 := by
    let v := hB.eigenvectorBasis rfl i
    have hv : ‖v‖=1 := (hB.eigenvectorBasis rfl).orthonormal.norm_eq_one i
    have he : B v=(a i : ℂ) • v :=
      Module.End.mem_eigenspace_iff.mp (hB.hasEigenvector_eigenvectorBasis rfl i).1
    have hn := B.le_opNorm v
    rw [he,norm_smul,hv,mul_one,mul_one,Complex.norm_real,Real.norm_eq_abs] at hn
    exact hn.trans hBn
  exact noisyCorrectionPolynomial_error hκ hδ hsmall hη hη1 ha (hgap i)

/-- Actual high correction turns the regularized inverse into the truncated
inverse. This is a proved spectral identity, not an assumed inverse certificate. -/
theorem highCorrection_resolvent_identity (B : E →L[ℂ] E)
    (hB : B.toLinearMap.IsSymmetric) {κ δ : ℝ} (hκ : 0<κ) (hδ : 0≤δ) :
    highCorrection B hB κ δ * B * Ring.inverse
      (B^2+(((2*κ)⁻¹)^2 : ℂ) • (1 : E →L[ℂ] E)) =
      (1/4 : ℂ) • highInverse B hB δ := by
  let U := (hB.eigenvectorBasis rfl).repr
  let a := hB.eigenvalues rfl
  let t := (2*κ)⁻¹
  have ht : 0<t := by dsimp [t]; positivity
  have hd : ∀ x i, U (B x) i=(a i : ℂ)*U x i :=
    fun x i => hB.eigenvectorBasis_apply_self_apply rfl x i
  rw [(resolvent_inverse U B a hd ht).2]
  conv_lhs => lhs; rhs; rw [operator_eq_conjugate U B a hd]
  change conjugate U _*conjugate U _*conjugate U _=(1/4:ℂ) • conjugate U _
  rw [← map_mul,← map_mul,← conjugate_smul]
  congr 1
  ext x i
  simp only [ContinuousLinearMap.mul_apply,Geometry.diagonal_apply,
    ContinuousLinearMap.smul_apply,PiLp.smul_apply,smul_eq_mul]
  change (highCorrectionValue κ δ (a i) : ℂ)*((a i : ℂ)*
    ((((a i^2+t^2)⁻¹ : ℝ) : ℂ)*x i)) =
      (1/4 : ℂ)*((if |a i|≤δ then (0:ℂ) else (((a i)⁻¹ : ℝ) : ℂ)) * x i)
  by_cases hi : |a i|≤δ
  · simp [highCorrectionValue,hi]
  · have ha : a i ≠ 0 := by intro hz; simp [hz,hδ] at hi
    have hac : (a i : ℂ) ≠ 0 := by exact_mod_cast ha
    have htden : (a i : ℂ)^2+(t : ℂ)^2 ≠ 0 := by
      exact_mod_cast ne_of_gt (show 0<a i^2+t^2 by positivity)
    simp only [highCorrectionValue,hi,if_false]
    change (((1+t^2/a i^2)/4 : ℝ) : ℂ)*((a i : ℂ)*
      ((((a i^2+t^2)⁻¹ : ℝ) : ℂ)*x i))=(1/4 : ℂ)*((((a i)⁻¹ : ℝ) : ℂ)*x i)
    push_cast
    field_simp

/-- Uniform operator norm of the actual computed correction. -/
theorem noisyCorrection_operator_norm (B : E →L[ℂ] E) (hB : B.toLinearMap.IsSymmetric)
    (hBn : ‖B‖≤1) {κ η : ℝ} (hκ : 2≤κ) (hη : 0<η) (hη1 : η<1/2) :
    ‖polynomialOperator (noisyCorrectionPolynomial κ η) B‖≤3/4 := by
  let U := (hB.eigenvectorBasis rfl).repr
  let a := hB.eigenvalues rfl
  have hd : ∀ x i, U (B x) i=(a i : ℂ)*U x i :=
    fun x i => hB.eigenvectorBasis_apply_self_apply rfl x i
  apply polynomialOperator_norm_le U B a hd _ (by norm_num)
  intro i
  apply noisyCorrectionPolynomial_bounded hκ hη hη1
  let v := hB.eigenvectorBasis rfl i
  have hv : ‖v‖=1 := (hB.eigenvectorBasis rfl).orthonormal.norm_eq_one i
  have he : B v=(a i : ℂ) • v :=
    Module.End.mem_eigenspace_iff.mp (hB.hasEigenvector_eigenvectorBasis rfl i).1
  have hn := B.le_opNorm v
  rw [he,norm_smul,hv,mul_one,mul_one,Complex.norm_real,Real.norm_eq_abs] at hn
  exact hn.trans hBn

end Operator

theorem noisyCorrectionPolynomial_degree {κ η : ℝ}
    (hκ : 2≤κ) (hη : 0<η) (hη1 : η<1/2) :
    ((noisyCorrectionPolynomial κ η).natDegree : ℝ)≤8501000000*κ*Real.log (1/η) := by
  have hp := noisyHighPass_degree (by linarith : 1≤κ) hη hη1
  have hc := (lemma54_correction_polynomial (κ := 2*κ) (by linarith) hη hη1).2.2.2
  have hm : ((noisyCorrectionPolynomial κ η).natDegree : ℝ)≤
      (noisyHighPass κ η).natDegree+(paperCorrectionPolynomial (2*κ) η).natDegree := by
    exact_mod_cast (natDegree_mul_le (p := noisyHighPass κ η) (q := paperCorrectionPolynomial (2*κ) η))
  have hlog : 0≤Real.log (1/η) := Real.log_nonneg ((le_div_iff₀ hη).mpr (by linarith))
  nlinarith [mul_nonneg (show 0≤κ by linarith) hlog]

/-- The implemented correction is one actual original-oracle single-flag QSVT
circuit; its work gates depend on signal width only. -/
theorem noisyCorrection_single_flag
    {D W : Type*} [Fintype D] [DecidableEq D] [Nonempty D] [Fintype W] [DecidableEq W]
    (a : ℕ) {κ η : ℝ} (hκ : 2≤κ) (hη : 0<η) (hη1 : η<1/2) :
    ∃ out : SingleFlagCircuit a D W,
      ((out.toQuery (SingleFlagGate.eval a)).matrixQueries : ℝ)≤34004000000*κ*Real.log (1/η) ∧
      (out.toQuery (SingleFlagGate.eval a)).vectorQueries=0 ∧
      (out.workGates : ℝ)≤150000000000000*κ*(a+1)*Real.log (1/η) ∧
      out.CallsOnly (originalSingleFlagPort a D) ∧
      ∀ (UA : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup W ℂ)
        (B : Matrix D D ℂ), B.IsHermitian → IsBlockEncoding (fun _ : Fin a => false) 1 0 UA B →
        IsBlockEncoding (physicalZero a) 1 0 ((out.toQuery (SingleFlagGate.eval a)).eval UA Ub)
          (Polynomial.aeval B (liftReal (noisyCorrectionPolynomial κ η))) := by
  obtain ⟨out,hm,hv,hg,hp,he⟩ := lemma24_single_flag_encoding (D := D) (B := W) a
    (noisyCorrectionPolynomial κ η) (noisyCorrectionPolynomial_even hκ hη hη1)
    (fun x hx => (noisyCorrectionPolynomial_bounded hκ hη hη1 hx).trans (by norm_num))
  have hd := noisyCorrectionPolynomial_degree hκ hη hη1
  have hl := kappa_log_ge_one hκ hη hη1
  refine ⟨out,?_,hv,?_,hp,he⟩
  · have hm' : ((out.toQuery (SingleFlagGate.eval a)).matrixQueries : ℝ)≤4*(noisyCorrectionPolynomial κ η).natDegree := by exact_mod_cast hm
    nlinarith
  · have hg' : (out.workGates : ℝ)≤15848*((noisyCorrectionPolynomial κ η).natDegree+1)*(a+1) := by exact_mod_cast hg
    have hmul := mul_le_mul_of_nonneg_right hd (show 0≤15848*((a:ℝ)+1) by positivity)
    have hmul' := mul_le_mul_of_nonneg_right hl (show 0≤15848*((a:ℝ)+1) by positivity)
    nlinarith

end OptimalQLS.PhysicalRobustness
