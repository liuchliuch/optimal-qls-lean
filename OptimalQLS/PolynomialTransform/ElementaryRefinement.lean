import OptimalQLS.PolynomialTransform.ElementaryEncoding
import OptimalQLS.PolynomialTransform.RefinementTheorems

/-! # Elementary-circuit endpoints for the paper's kernel and correction filters -/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Polynomial Matrix DirtyAncilla
open scoped Matrix.Norms.L2Operator
variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

/-- Lemma 5.5 with an actual elementary circuit, exact polynomial encoding,
original-coordinate inverse-square error, and both resource bounds. -/
theorem lemma55_correction_elementary_circuit [Nonempty D] (a : ℕ)
    {κ η : ℝ} (hκ : 2 ≤ κ) (hη0 : 0 < η) (hη1 : η < 1/2) :
    ∃ c : ElementaryCircuit ((Fin a → Bool) × D) B (QSVTWire a) D,
      (c.toQuery.matrixQueries : ℝ) ≤ 840000*κ*Real.log (1/η) ∧ c.toQuery.vectorQueries=0 ∧
      (c.workGates : ℝ) ≤ 6248*(210000*κ*Real.log (1/η)+1)*(a+1) ∧
      ∀ (U : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ)
        (A : Matrix D D ℂ), A.IsHermitian → IsUnit A →
        IsBlockEncoding (fun _ : Fin a => false) 1 0 U A → ‖Ring.inverse A‖ ≤ κ →
        IsBlockEncoding (physicalZero a) 1 0 (c.toQuery.eval U Ub)
          (Polynomial.aeval A (liftReal (paperCorrectionPolynomial κ η))) ∧
        ‖signalBlock (physicalZero a) (c.toQuery.eval U Ub)-
          (1/4 : ℂ) • (1+((κ⁻¹)^2 : ℂ) • (Ring.inverse A)^2)‖ ≤ η/2 := by
  have hp := lemma54_correction_polynomial hκ hη0 hη1
  obtain ⟨c,hq,hv,hg,henc⟩ := lemma24_elementary_encoding (D := D) (B := B) a
    (paperCorrectionPolynomial κ η) hp.1 (fun x hx => (hp.2.1 x hx).trans (by norm_num))
  refine ⟨c,?_,hv,?_,?_⟩
  · have hq' : (c.toQuery.matrixQueries : ℝ) ≤ 4*(paperCorrectionPolynomial κ η).natDegree := by
      exact_mod_cast hq
    nlinarith [hp.2.2.2]
  · have hg' : (c.workGates : ℝ) ≤
        6248*((paperCorrectionPolynomial κ η).natDegree+1)*(a+1) := by exact_mod_cast hg
    refine hg'.trans ?_
    gcongr
    exact hp.2.2.2
  · intro U Ub A hA hu hb hi
    have he := henc U Ub A hA hb
    refine ⟨he,?_⟩
    have hblock := exact_block_eq he
    rw [one_smul] at hblock
    rw [← hblock]
    exact lemma55_correction_matrix_error A hA hu hκ hη0 hη1 (norm_le_of_exact_block hb) hi

/-- Lemma 5.2's kernel-filter circuit for a proved spectral gap: actual one-
and two-qubit gates, no vector calls, and approximation to the actual kernel projection. -/
theorem lemma52_kernel_elementary_circuit [Nonempty D] (a : ℕ)
    {δ η : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1/Real.sqrt 12) (hη0 : 0 < η) (hη1 : η < 1/2) :
    ∃ c : ElementaryCircuit ((Fin a → Bool) × D) B (QSVTWire a) D,
      (c.toQuery.matrixQueries : ℝ) < 24*δ⁻¹*Real.log (1/η) ∧ c.toQuery.vectorQueries=0 ∧
      (c.workGates : ℝ) ≤ 6248*(6*δ⁻¹*Real.log (1/η)+1)*(a+1) ∧
      ∀ (U : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ)
        (A : Matrix D D ℂ), A.IsHermitian → IsBlockEncoding (fun _ : Fin a => false) 1 0 U A →
        (∀ μ : ℂ, μ ∈ spectrum ℂ (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A).toLinearMap →
          μ ≠ 0 → δ ≤ ‖μ‖ ∧ ‖μ‖ ≤ 1) →
        IsBlockEncoding (physicalZero a) 1 0 (c.toQuery.eval U Ub)
          (Polynomial.aeval A (liftReal (kernelFilter δ η))) ∧
        ‖Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (signalBlock (physicalZero a) (c.toQuery.eval U Ub))-
          (LinearMap.ker (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A).toLinearMap).starProjection‖ ≤ η := by
  have hp := lemma51_kernel_filter hδ0 hδ1 hη0 hη1
  have hd := kernelFilter_degree_complexity hδ0 hδ1 hη0 hη1
  obtain ⟨c,hq,hv,hg,henc⟩ := lemma24_elementary_encoding (D := D) (B := B) a
    (kernelFilter δ η) hp.1 hp.2.2.2.1
  refine ⟨c,?_,hv,?_,?_⟩
  · have hq' : (c.toQuery.matrixQueries : ℝ) ≤ 4*(kernelFilter δ η).natDegree := by exact_mod_cast hq
    nlinarith
  · have hg' : (c.workGates : ℝ) ≤ 6248*((kernelFilter δ η).natDegree+1)*(a+1) := by exact_mod_cast hg
    refine hg'.trans ?_
    gcongr
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
