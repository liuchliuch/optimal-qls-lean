import OptimalQLS.PolynomialTransform.QueryEncoding
import OptimalQLS.PolynomialTransform.GraphFilter
import OptimalQLS.InverseSquare.Optimal

/-! # Unconditional scalar correction and concrete matrix-only refinement query circuits -/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Polynomial Matrix
open scoped Matrix.Norms.L2Operator

/-- The actual correction polynomial, with its inverse-square construction filled in. -/
def paperCorrectionPolynomial (κ η : ℝ) : ℝ[X] :=
  correctionPolynomial (InverseSquare.inverseSquarePolynomial κ⁻¹ η)

/-- Lemma 5.4 with no polynomial-approximation existence premise. -/
theorem lemma54_correction_polynomial {κ η : ℝ} (hκ : 2 ≤ κ) (hη0 : 0 < η) (hη1 : η < 1/2) :
    Function.Even (paperCorrectionPolynomial κ η).eval ∧
    (∀ x : ℝ, |x| ≤ 1 → |(paperCorrectionPolynomial κ η).eval x| ≤ 3/4) ∧
    (∀ x : ℝ, κ⁻¹ ≤ |x| → |x| ≤ 1 →
      |(paperCorrectionPolynomial κ η).eval x-(1+(κ⁻¹)^2/x^2)/4| ≤ η/2) ∧
    ((paperCorrectionPolynomial κ η).natDegree : ℝ) ≤ 210000*κ*Real.log (1/η) := by
  have hk : 0 < κ := by linarith
  have hd0 : 0 < κ⁻¹ := inv_pos.mpr hk
  have hd1 : κ⁻¹ ≤ (1/2 : ℝ) := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hk).mpr (by linarith)
  refine ⟨correctionPolynomial_even (InverseSquare.inverseSquarePolynomial_even _ _),?_,?_,?_⟩
  · intro x hx
    exact correctionPolynomial_bounded (InverseSquare.inverseSquarePolynomial_bounded hd0 hd1 hη0 hx)
  · intro x hx0 hx1
    exact correctionPolynomial_error (InverseSquare.inverseSquarePolynomial_error hd0 hd1 hη0 hx0 hx1)
  · have hdeg := correctionPolynomial_degree (InverseSquare.inverseSquarePolynomial κ⁻¹ η)
    have hdeg' : ((paperCorrectionPolynomial κ η).natDegree : ℝ) ≤
        (InverseSquare.inverseSquarePolynomial κ⁻¹ η).natDegree := by exact_mod_cast hdeg
    exact hdeg'.trans (by simpa using InverseSquare.inverseSquarePolynomial_degree hd0 hd1 hη0 hη1)

variable {S D B : Type*} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B]

/-- The correction bound for actual matrices and actual nonsingular inverse. -/
theorem lemma55_correction_matrix_error (A : Matrix D D ℂ) (hA : A.IsHermitian) (hunit : IsUnit A)
    {κ η : ℝ} (hκ : 2 ≤ κ) (hη0 : 0 < η) (hη1 : η < 1/2)
    (hAnorm : ‖A‖ ≤ 1) (hinorm : ‖Ring.inverse A‖ ≤ κ) :
    ‖Polynomial.aeval A (liftReal (paperCorrectionPolynomial κ η))-
      (1/4 : ℂ) • (1+((κ⁻¹)^2 : ℂ) • (Ring.inverse A)^2)‖ ≤ η/2 := by
  let φ := Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)
  have hs : (φ A).toLinearMap.IsSymmetric := Matrix.isHermitian_iff_isSymmetric.mp hA
  have hu : IsUnit (φ A) := hunit.map φ.toMonoidHom
  have hi := OptimalQLS.Perturbation.toEuclideanCLM_inverse A hunit
  have hin : ‖Ring.inverse (φ A)‖ ≤ κ := by rw [← hi]; exact hinorm
  have hk : 0 < κ := by linarith
  have hd0 : 0 < κ⁻¹ := inv_pos.mpr hk
  have hd1 : κ⁻¹ ≤ (1/2 : ℝ) := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hk).mpr (by linarith)
  have herr := correctionOperator_distance (φ A) hs hu hk hAnorm hin hη0.le
    (InverseSquare.inverseSquarePolynomial κ⁻¹ η)
    (fun x hx0 hx1 => InverseSquare.inverseSquarePolynomial_error hd0 hd1 hη0 hx0 hx1)
  change ‖polynomialOperator (paperCorrectionPolynomial κ η) (φ A)-idealCorrection (φ A) κ‖ ≤ η/2 at herr
  have ht : φ ((1/4 : ℂ) • (1+((κ⁻¹)^2 : ℂ) • (Ring.inverse A)^2))=idealCorrection (φ A) κ := by
    simp only [map_smul,map_add,map_one,map_pow,idealCorrection]
    rw [hi]
  rw [← polynomial_matrix_to_operator A (paperCorrectionPolynomial κ η),← ht,← map_sub] at herr
  exact herr

/-- The actual correction matrix has the uniform three-quarter norm bound. -/
theorem lemma55_correction_matrix_norm (A : Matrix D D ℂ) (hA : A.IsHermitian)
    (hAnorm : ‖A‖ ≤ 1) {κ η : ℝ} (hκ : 2 ≤ κ) (hη0 : 0 < η) :
    ‖Polynomial.aeval A (liftReal (paperCorrectionPolynomial κ η))‖ ≤ 3/4 := by
  have hk : 0 < κ := by linarith
  have hd0 : 0 < κ⁻¹ := inv_pos.mpr hk
  have hd1 : κ⁻¹ ≤ (1/2 : ℝ) := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hk).mpr (by linarith)
  have hs : (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A).toLinearMap.IsSymmetric :=
    Matrix.isHermitian_iff_isSymmetric.mp hA
  have h := correctionOperator_norm_le (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A)
    hs hAnorm (InverseSquare.inverseSquarePolynomial κ⁻¹ η)
    (fun x hx => InverseSquare.inverseSquarePolynomial_bounded hd0 hd1 hη0 hx)
  change ‖polynomialOperator (paperCorrectionPolynomial κ η)
    (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A)‖ ≤ 3/4 at h
  rw [← polynomial_matrix_to_operator] at h
  exact h

/-- Lemma 5.5: a concrete exact correction query circuit, its original-matrix
operator error, and explicit O(κ log(1/η)) matrix-only query bound. -/
theorem lemma55_correction_query_circuit [Nonempty D] (s₀ : S)
    {κ η : ℝ} (hκ : 2 ≤ κ) (hη0 : 0 < η) (hη1 : η < 1/2) :
    ∃ c : QueryCircuit (S × D) B (((Bool × Bool) × S) × D),
      (c.matrixQueries : ℝ) ≤ 840000*κ*Real.log (1/η) ∧ c.vectorQueries=0 ∧
      ∀ (U : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ) (A : Matrix D D ℂ),
        A.IsHermitian → IsUnit A → IsBlockEncoding s₀ 1 0 U A → ‖Ring.inverse A‖ ≤ κ →
        IsBlockEncoding ((false,false),s₀) 1 0 (c.eval U Ub)
          (Polynomial.aeval A (liftReal (paperCorrectionPolynomial κ η))) ∧
        ‖signalBlock ((false,false),s₀) (c.eval U Ub)-
          (1/4 : ℂ) • (1+((κ⁻¹)^2 : ℂ) • (Ring.inverse A)^2)‖ ≤ η/2 := by
  have hp := lemma54_correction_polynomial hκ hη0 hη1
  obtain ⟨c,hq,hv,henc⟩ := lemma24_exact_query_encoding (D := D) (B := B) s₀
    (paperCorrectionPolynomial κ η) hp.1 (fun x hx => (hp.2.1 x hx).trans (by norm_num))
  refine ⟨c,?_,hv,?_⟩
  · have hq' : (c.matrixQueries : ℝ) ≤ 4*(paperCorrectionPolynomial κ η).natDegree := by exact_mod_cast hq
    nlinarith [hp.2.2.2]
  · intro U Ub A hA hu hb hi
    have he := henc U Ub A hA hb
    refine ⟨he,?_⟩
    have hblock := exact_block_eq he
    rw [one_smul] at hblock
    rw [← hblock]
    exact lemma55_correction_matrix_error A hA hu hκ hη0 hη1 (norm_le_of_exact_block hb) hi

/-- Concrete filter circuit for a spectral gap, with no vector-oracle access.
The graph-specific parameter and spectrum estimates are proved in GraphFilter. -/
theorem lemma52_kernel_query_circuit [Nonempty D] (s₀ : S)
    {δ η : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1/Real.sqrt 12) (hη0 : 0 < η) (hη1 : η < 1/2) :
    ∃ c : QueryCircuit (S × D) B (((Bool × Bool) × S) × D),
      (c.matrixQueries : ℝ) < 24*δ⁻¹*Real.log (1/η) ∧ c.vectorQueries=0 ∧
      ∀ (U : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ) (A : Matrix D D ℂ),
        A.IsHermitian → IsBlockEncoding s₀ 1 0 U A →
        (∀ μ : ℂ, μ ∈ spectrum ℂ (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A).toLinearMap →
          μ ≠ 0 → δ ≤ ‖μ‖ ∧ ‖μ‖ ≤ 1) →
        IsBlockEncoding ((false,false),s₀) 1 0 (c.eval U Ub) (Polynomial.aeval A (liftReal (kernelFilter δ η))) ∧
        ‖Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (signalBlock ((false,false),s₀) (c.eval U Ub))-
          (LinearMap.ker (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A).toLinearMap).starProjection‖ ≤ η := by
  have hp := lemma51_kernel_filter hδ0 hδ1 hη0 hη1
  obtain ⟨c,hq,hv,henc⟩ := lemma24_exact_query_encoding (D := D) (B := B) s₀
    (kernelFilter δ η) hp.1 hp.2.2.2.1
  refine ⟨c,?_,hv,?_⟩
  · have hq' : (c.matrixQueries : ℝ) ≤ 4*(kernelFilter δ η).natDegree := by exact_mod_cast hq
    have hd := kernelFilter_degree_complexity hδ0 hδ1 hη0 hη1
    nlinarith
  · intro U Ub A hA hb hspec
    have he := henc U Ub A hA hb
    refine ⟨he,?_⟩
    have hblock := exact_block_eq he
    rw [one_smul] at hblock
    rw [← hblock,polynomial_matrix_to_operator]
    have hs : (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A).toLinearMap.IsSymmetric :=
      Matrix.isHermitian_iff_isSymmetric.mp hA
    exact kernelFilter_operator_bound (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A)
      hs hδ0 hδ1 hη0 hη1 hspec

end OptimalQLS.PolynomialTransform
