import OptimalQLS.PhysicalRobustness.RegularizerPolynomial
import OptimalQLS.PhysicalRobustness.PerturbedGap
import OptimalQLS.PolynomialTransform.SingleFlagPaperTheorems

/-! Actual polynomial and single-flag implementation of noisy spectral truncation. -/
noncomputable section
namespace OptimalQLS.PhysicalRobustness
open Polynomial Geometry PolynomialTransform Matrix PhysicalPadding
open scoped Matrix.Norms.L2Operator

/-- The original noise threshold implies the constant regularizer thresholds. -/
theorem noisyHighPass_scalar {κ δ η x : ℝ}
    (hκ : 0<κ) (hδ : 0≤δ) (hsmall : κ*δ≤1/4) (hη : 0<η) (hx : |x|≤1) :
    (|x|≤δ → |(noisyHighPass κ η).eval x|≤η) ∧
    (κ⁻¹-δ≤|x| → |(noisyHighPass κ η).eval x-1|≤η) := by
  have hi : (2*κ)⁻¹=κ⁻¹/2 := by field_simp
  have hd : δ≤κ⁻¹/4 := by
    rw [inv_eq_one_div, div_div]
    apply (le_div_iff₀ (by positivity : (0:ℝ)<κ*4)).mpr
    nlinarith
  have hb := regularizerPolynomial_bounded (κ := 2*κ) (by positivity) hx
  constructor
  · intro hl
    rw [noisyHighPass, eval_comp]
    apply stepPolynomial_low hη
    apply regularizerPolynomial_low (by positivity) hx
    rw [hi]
    linarith
  · intro hh
    rw [noisyHighPass, eval_comp]
    apply stepPolynomial_high hη _ hb
    apply regularizerPolynomial_high (by positivity) hx
    rw [hi]
    linarith

section Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- The computed high-pass polynomial approximates the actual spectral
projection, uniformly in operator norm. -/
theorem noisyHighPass_operator_error (B : E →L[ℂ] E) (hB : B.toLinearMap.IsSymmetric)
    (hBn : ‖B‖≤1) {κ δ η : ℝ} (hκ : 0<κ) (hδ : 0≤δ) (hsmall : κ*δ≤1/4)
    (hη : 0<η)
    (hgap : ∀ i, |hB.eigenvalues rfl i|≤δ ∨ κ⁻¹-δ≤|hB.eigenvalues rfl i|) :
    ‖polynomialOperator (noisyHighPass κ η) B-(1-lowProjector B hB δ)‖≤η := by
  let U := (hB.eigenvectorBasis rfl).repr
  let a := hB.eigenvalues rfl
  have hd : ∀ x i, U (B x) i=(a i : ℂ)*U x i :=
    fun x i => hB.eigenvectorBasis_apply_self_apply rfl x i
  have ha (i) : |a i|≤1 := by
    let v := hB.eigenvectorBasis rfl i
    have hv : ‖v‖=1 := (hB.eigenvectorBasis rfl).orthonormal.norm_eq_one i
    have he : B v=(a i : ℂ) • v :=
      Module.End.mem_eigenspace_iff.mp (hB.hasEigenvector_eigenvectorBasis rfl i).1
    have hn := B.le_opNorm v
    rw [he,norm_smul,hv,mul_one,mul_one,Complex.norm_real,Real.norm_eq_abs] at hn
    exact hn.trans hBn
  have heq : 1-lowProjector B hB δ =
      conjugate U (Geometry.diagonal (fun i => ((if |a i|≤δ then 0 else 1 : ℝ) : ℂ))) := by
    unfold lowProjector
    rw [← map_one (conjugate U),← map_sub]
    congr 1
    ext x i
    by_cases hi : |a i|≤δ <;> simp [U,a,hi]
  rw [heq]
  apply polynomial_diagonal_distance U B a hd _ _ hη.le
  intro i
  have hs := noisyHighPass_scalar hκ hδ hsmall hη (ha i)
  by_cases hi : |a i|≤δ
  · simpa [hi] using hs.1 hi
  · simpa [hi] using hs.2 ((hgap i).resolve_left hi)
end Operator

/-- No spectral-gap premise remains when the polynomial is applied to the
actual perturbed zero extension. -/
theorem physical_noisyHighPass_error
    {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]
    (f : D ↪ P) (A : Matrix D D ℂ) (hA : A.IsHermitian) (hunit : IsUnit A)
    (B : Matrix P P ℂ) (hB : B.IsHermitian) (hBn : ‖B‖≤1)
    {κ δ η : ℝ} (hκ : 0<κ) (hδ : 0≤δ) (hsmall : κ*δ≤1/4) (hη : 0<η)
    (hinv : ‖Ring.inverse A‖≤κ) (hpert : ‖B-zeroExtend f A‖≤δ) :
    ‖polynomialOperator (noisyHighPass κ η) (Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) B)-
      (1-lowProjector (Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) B)
        (matrixHermitian_symmetric B hB) δ)‖≤η := by
  let H := Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) (zeroExtend f A)
  let C := Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) B
  have hH : H.toLinearMap.IsSymmetric := matrixHermitian_symmetric _ (zeroExtend_hermitian f A hA)
  have hC : C.toLinearMap.IsSymmetric := matrixHermitian_symmetric B hB
  have he : ‖C-H‖≤δ := by
    change ‖Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) B-
      Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) (zeroExtend f A)‖≤δ
    rw [← map_sub]
    exact hpert
  apply noisyHighPass_operator_error C hC hBn hκ hδ hsmall hη
  exact noisy_spectral_gap H C hH hC hδ (zeroExtend_spectral_gap f A hunit hH hκ hinv) he

/-- A concrete original-oracle single-flag circuit implementing the high-pass
polynomial. Its work bound has no data-register-size factor. -/
theorem noisyHighPass_single_flag
    {D W : Type*} [Fintype D] [DecidableEq D] [Nonempty D] [Fintype W] [DecidableEq W]
    (a : ℕ) {κ η : ℝ} (hκ : 2≤κ) (hη : 0<η) (hη1 : η<1/2) :
    ∃ out : SingleFlagCircuit a D W,
      ((out.toQuery (SingleFlagGate.eval a)).matrixQueries : ℝ)≤34000000000*κ*Real.log (1/η) ∧
      (out.toQuery (SingleFlagGate.eval a)).vectorQueries=0 ∧
      (out.workGates : ℝ)≤140000000000000*κ*(a+1)*Real.log (1/η) ∧
      out.CallsOnly (originalSingleFlagPort a D) ∧
      ∀ (UA : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup W ℂ)
        (B : Matrix D D ℂ), B.IsHermitian → IsBlockEncoding (fun _ : Fin a => false) 1 0 UA B →
        IsBlockEncoding (physicalZero a) 1 0 ((out.toQuery (SingleFlagGate.eval a)).eval UA Ub)
          (Polynomial.aeval B (liftReal (noisyHighPass κ η))) := by
  have hk : 0<κ := by linarith
  obtain ⟨out,hm,hv,hg,hp,he⟩ := lemma24_single_flag_encoding (D := D) (B := W) a
    (noisyHighPass κ η) (noisyHighPass_even κ η) (fun x hx => noisyHighPass_bounded hk η hx)
  have hd := noisyHighPass_degree (by linarith : 1≤κ) hη hη1
  have hl := kappa_log_ge_one hκ hη hη1
  refine ⟨out,?_,hv,?_,hp,he⟩
  · have hm' : ((out.toQuery (SingleFlagGate.eval a)).matrixQueries : ℝ)≤4*(noisyHighPass κ η).natDegree := by exact_mod_cast hm
    nlinarith
  · have hg' : (out.workGates : ℝ)≤15848*((noisyHighPass κ η).natDegree+1)*(a+1) := by exact_mod_cast hg
    have hmul := mul_le_mul_of_nonneg_right hd (show 0≤15848*((a:ℝ)+1) by positivity)
    have hmul' := mul_le_mul_of_nonneg_right hl (show 0≤15848*((a:ℝ)+1) by positivity)
    nlinarith

end OptimalQLS.PhysicalRobustness
