import OptimalQLS.PhysicalRobustness.PhysicalProgram.Circuit

/-! Actual noisy-program acceptance on arbitrary active embeddings and full oracles. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open scoped Classical Matrix.Norms.L2Operator
namespace OptimalQLS.PhysicalRobustness.PhysicalProgram
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform PhysicalPadding Refinement
open Refinement.PhysicalProgram
variable {a n : ℕ} {κ ŝ ε : ℝ}

/-- Exact accepted-vector identity for the same literal preparation/filter/correction
lists whose counts and local ports were proved. -/
theorem Implementation.accepted_eq (I : Implementation a n κ ŝ ε)
    {t : ℝ} (h : BudgetParameters (2*κ) t (9*ŝ/8))
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (B : Matrix (Bits n) (Bits n) ℂ) (hB : B.IsHermitian)
    (henc : IsBlockEncoding (fun _ : Fin a=>false) 1 0 UA B) :
    I.accepted UA Ub=noisyCorrectionOperator B κ (ε/4096)
      (graphCoordinate 2 (Matrix.toEuclideanCLM (n := Fin 4 × Bits n) (𝕜 := ℂ)
        (signalBlock (physicalZero (a+4)) ((I.filter.toQuery (GraphAttachedGate.eval a)).eval UA Ub))
        (WithLp.toLp 2 (Alignment.zeroAuxiliaryOutput
          (GraphEncoding.physicalSignalZero (fun _ : Fin a=>false))
          (originalPreparedState (fun _ : Fin a=>false) (fun _ : Fin n=>false) h UA Ub))))) := by
  have hc := exact_block_eq (I.correction_block UA Ub B hB henc)
  rw [one_smul] at hc
  unfold Implementation.accepted acceptedVector
  rw [program_prepared_state a n h I.preparation I.filter I.correction (I.preparation_state t h)]
  rw [refinementProgram_acceptance,coarseVector_slice,←hc]
  change Matrix.toEuclideanCLM (n := Bits n) (𝕜 := ℂ)
    (Polynomial.aeval B (liftReal (noisyCorrectionPolynomial κ (ε/4096))))
    (graphCoordinate 2 (Matrix.toEuclideanCLM (n := Fin 4 × Bits n) (𝕜 := ℂ)
      (signalBlock (physicalZero (a+4)) ((I.filter.toQuery (GraphAttachedGate.eval a)).eval UA Ub))
      (WithLp.toLp 2 (Alignment.zeroAuxiliaryOutput
        (GraphEncoding.physicalSignalZero (fun _ : Fin a=>false))
        (originalPreparedState (fun _ : Fin a=>false) (fun _ : Fin n=>false) h UA Ub))))) = _
  rw [polynomial_matrix_to_operator]
  rfl

/-- Correctness is for the actual arbitrary Hermitian physical block B, with no
support-preservation, active-subspace invariance, or global invertibility promise. -/
theorem Implementation.correctness (I : Implementation a n κ ŝ ε)
    {D : Type*} [Fintype D] [DecidableEq D] (f : D ↪ Bits n)
    (A : Matrix D D ℂ) (hA : A.IsHermitian) (hunit : IsUnit A) (hAnorm : ‖A‖≤1)
    (B : Matrix (Bits n) (Bits n) ℂ) (hB : B.IsHermitian)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (henc : IsBlockEncoding (fun _ : Fin a=>false) 1 0 UA B)
    (Ub : Matrix.unitaryGroup (Bits n) ℂ) (b : EuclideanSpace ℂ D) (hb : ‖b‖=1)
    (hcol : ∀ i,Ub i (fun _ : Fin n=>false)=coordinateIsometry f b i)
    {δ : ℝ} (hδ : 0≤δ) (hinv : ‖Ring.inverse A‖≤κ)
    (hpert : ‖B-zeroExtend f A‖≤δ) (hsmall : κ*δ≤1/4)
    (hestlo : solutionScale 1 A b/2≤ŝ) (hesthi : ŝ≤2*solutionScale 1 A b)
    (hε : 0<ε) (hε1 : ε<1/2) :
    let v := highInverse (Matrix.toEuclideanCLM (n := Bits n) (𝕜 := ℂ) B)
      (matrixHermitian_symmetric B hB) δ (coordinateIsometry f b)
    I.accepted UA Ub≠0 ∧
      ‖NormedSpace.normalize (I.accepted UA Ub)-NormedSpace.normalize v‖≤ε/2 ∧
      1/262144<‖I.accepted UA Ub‖^2 ∧ ‖I.accepted UA Ub‖^2≤1 := by
  obtain ⟨h,hprep⟩ := noisy_original_preparation_coarse f (fun _ : Fin a=>false)
    (fun _ : Fin n=>false) A hA hunit hAnorm B hB UA henc Ub b hb hcol
    I.kappa_ge_two hδ hinv hpert hsmall hestlo hesthi
  dsimp only at hprep
  obtain ⟨hn,β,hβ0,hβ1,hPy,_⟩ := hprep
  have hy := (zeroAuxiliaryOutput_norm_le (GraphEncoding.physicalSignalZero (fun _ : Fin a=>false))
    (originalPreparedState (fun _ : Fin a=>false) (fun _ : Fin n=>false) h UA Ub)).trans_eq hn
  have herr := noisy_refinement_component_guarantee f A hA hunit hAnorm B hB
    (norm_le_of_exact_block henc) b hb I.kappa_ge_two hδ hinv hpert hsmall hestlo hesthi hε hε1
    _ hy hβ0.le hβ1 hPy _ (I.filter_semantics UA Ub B hB henc).2
  have hz := I.accepted_eq h UA Ub B hB henc
  dsimp only at herr ⊢
  rw [←hz] at herr
  exact ⟨herr.1,herr.2.1,herr.2.2,I.probability_le_one UA Ub⟩

/-- Valid factor-two estimates already imply the classical outer range used to
select the fixed program; the exact norm never selects a list. -/
theorem classical_estimate_range {D : Type*} [Fintype D] [DecidableEq D]
    (A : Matrix D D ℂ) (hunit : IsUnit A) (hAnorm : ‖A‖≤1)
    (b : EuclideanSpace ℂ D) (hb : ‖b‖=1) {κ ŝ : ℝ} (hinv : ‖Ring.inverse A‖≤κ)
    (hestlo : solutionScale 1 A b/2≤ŝ) (hesthi : ŝ≤2*solutionScale 1 A b) :
    1/2≤ŝ ∧ ŝ≤2*κ := by
  let T := Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A
  have hTu : IsUnit T := hunit.map (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)).toMonoidHom
  have hsEq : solutionScale 1 A b=‖Ring.inverse T b‖ := by
    simp only [solutionScale,one_mul]
    rw [Perturbation.toEuclideanCLM_inverse A hunit]
  have hTi : ‖Ring.inverse T‖≤κ := by
    rw [←Perturbation.toEuclideanCLM_inverse A hunit]
    exact hinv
  have hlo : 1≤‖Ring.inverse T b‖ := by
    have he := Perturbation.apply_inverse T hTu b
    have hn := T.le_opNorm (Ring.inverse T b)
    rw [he,hb] at hn
    have htN : ‖T‖≤1 := hAnorm
    have hm := mul_le_mul_of_nonneg_right htN (norm_nonneg (Ring.inverse T b))
    nlinarith
  have hhi : ‖Ring.inverse T b‖≤κ := by
    have hn := (Ring.inverse T).le_opNorm b
    rw [hb,mul_one] at hn
    exact hn.trans hTi
  rw [hsEq] at hestlo hesthi
  constructor <;> linarith

end OptimalQLS.PhysicalRobustness.PhysicalProgram
