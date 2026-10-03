import OptimalQLS.PhysicalPadding.Operators
import OptimalQLS.PolynomialTransform.SingleFlagPaperTheorems

/-! Strict QSVT of the arbitrary supplied padded oracle, with correction error
measured on the reducing active range rather than a fictitious global inverse. -/
noncomputable section
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
namespace OptimalQLS.PhysicalPadding
open Matrix Polynomial PolynomialTransform
open scoped Matrix.Norms.L2Operator
variable {D P B : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]
  [Fintype B] [DecidableEq B]

/-- The logical correction operator is embedded only on the active range. -/
def activeCorrection (f : D ↪ P) (A : Matrix D D ℂ) (κ : ℝ) : Matrix P P ℂ :=
  zeroExtend f ((1/4 : ℂ) • (1+((κ⁻¹)^2 : ℂ) • (Ring.inverse A)^2))

theorem physical_correction_error (f : D ↪ P) (A : Matrix D D ℂ) (hA : A.IsHermitian)
    (hunit : IsUnit A) {κ η : ℝ} (hκ : 2 ≤ κ) (hη0 : 0 < η) (hη1 : η < 1/2)
    (hAnorm : ‖A‖ ≤ 1) (hinorm : ‖Ring.inverse A‖ ≤ κ) (x : EuclideanSpace ℂ D) :
    ‖Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ)
        (Polynomial.aeval (zeroExtend f A) (liftReal (paperCorrectionPolynomial κ η)))
        (coordinateIsometry f x) -
      Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) (activeCorrection f A κ)
        (coordinateIsometry f x)‖ ≤ (η/2)*‖x‖ := by
  have he := lemma55_correction_matrix_error A hA hunit hκ hη0 hη1 hAnorm hinorm
  rw [polynomial_matrix_to_operator, zeroExtend_polynomial, activeCorrection, zeroExtend_apply,
    ← map_sub, (coordinateIsometry f).norm_map, ← polynomial_matrix_to_operator]
  let C := Polynomial.aeval A (liftReal (paperCorrectionPolynomial κ η))
  let I := (1/4 : ℂ) • (1+((κ⁻¹)^2 : ℂ) • (Ring.inverse A)^2)
  change ‖(Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) C) x -
    (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) I) x‖ ≤ _
  calc
    _ = ‖(Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (C-I)) x‖ := by rw [map_sub]; rfl
    _ ≤ ‖Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (C-I)‖*‖x‖ :=
      (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (C-I)).le_opNorm x
    _ ≤ (η/2)*‖x‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)

/-- The very same strict single-flag circuit implements correction on arbitrary
physical UA. Its bounds contain a, not the number of data qubits. -/
theorem physical_correction_single_flag [Nonempty D] [Nonempty P] (f : D ↪ P) (a : ℕ)
    {κ η : ℝ} (hκ : 2 ≤ κ) (hη0 : 0 < η) (hη1 : η < 1/2) :
    ∃ c : SingleFlagCircuit a P B,
      ((c.toQuery (SingleFlagGate.eval a)).matrixQueries : ℝ) ≤ 840000*κ*Real.log (1/η) ∧
      (c.toQuery (SingleFlagGate.eval a)).vectorQueries = 0 ∧
      (c.workGates : ℝ) ≤ 3328095848*κ*(a+1)*Real.log (1/η) ∧
      c.CallsOnly (originalSingleFlagPort a P) ∧
      ∀ (U : Matrix.unitaryGroup ((Fin a → Bool) × P) ℂ) (Ub : Matrix.unitaryGroup B ℂ)
        (A : Matrix D D ℂ), A.IsHermitian → IsUnit A →
        IsBlockEncoding (fun _ : Fin a => false) 1 0 U (zeroExtend f A) → ‖Ring.inverse A‖ ≤ κ →
        IsBlockEncoding (physicalZero a) 1 0 ((c.toQuery (SingleFlagGate.eval a)).eval U Ub)
          (Polynomial.aeval (zeroExtend f A) (liftReal (paperCorrectionPolynomial κ η))) ∧
        ∀ x : EuclideanSpace ℂ D,
        ‖Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ)
            (signalBlock (physicalZero a) ((c.toQuery (SingleFlagGate.eval a)).eval U Ub))
            (coordinateIsometry f x) -
          Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) (activeCorrection f A κ)
            (coordinateIsometry f x)‖ ≤ (η/2)*‖x‖ := by
  have hp := lemma54_correction_polynomial hκ hη0 hη1
  obtain ⟨c,hq,hv,hg,hports,henc⟩ := lemma24_single_flag_encoding (D := P) (B := B) a
    (paperCorrectionPolynomial κ η) hp.1 (fun x hx => (hp.2.1 x hx).trans (by norm_num))
  refine ⟨c,?_,hv,?_,hports,?_⟩
  · have hq' : ((c.toQuery (SingleFlagGate.eval a)).matrixQueries : ℝ) ≤
        4*(paperCorrectionPolynomial κ η).natDegree := by exact_mod_cast hq
    nlinarith [hp.2.2.2]
  · have hg' : (c.workGates : ℝ) ≤
        15848*((paperCorrectionPolynomial κ η).natDegree+1)*(a+1) := by exact_mod_cast hg
    have hl := kappa_log_ge_one hκ hη0 hη1
    calc
      _ ≤ 15848*(210000*κ*Real.log (1/η)+1)*(a+1) := hg'.trans (by gcongr; exact hp.2.2.2)
      _ ≤ 15848*(210001*(κ*Real.log (1/η)))*(a+1) := by gcongr; nlinarith
      _ = _ := by ring
  · intro U Ub A hA hu hU hi
    have he := henc U Ub (zeroExtend f A) (zeroExtend_hermitian f A hA) hU
    refine ⟨he,?_⟩
    intro x
    have hb := exact_block_eq he
    rw [one_smul] at hb
    rw [← hb]
    apply physical_correction_error f A hA hu hκ hη0 hη1 _ hi x
    rw [← zeroExtend_norm f A]
    exact norm_le_of_exact_block hU

end OptimalQLS.PhysicalPadding
