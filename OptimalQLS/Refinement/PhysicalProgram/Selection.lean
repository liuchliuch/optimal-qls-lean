import OptimalQLS.Refinement.PhysicalProgram.Circuit
import OptimalQLS.PhysicalPadding.Filter
import OptimalQLS.PhysicalPadding.Polynomial

/-! # One fixed triple of actual preparation/filter/correction witnesses -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.Refinement.PhysicalProgram
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform PhysicalPadding

/-- Correction's exact polynomial implementation is uniform over every full
Hermitian physical block, including all singular zero extensions. -/
theorem correction_uniform (a n : ℕ) {κ η : ℝ}
    (hκ : 2≤κ) (hη0 : 0<η) (hη1 : η<1/2) :
    ∃ cc : SingleFlagCircuit a (Bits n) (Bits n),
      ((cc.toQuery (SingleFlagGate.eval a)).matrixQueries : ℝ)≤840000*κ*Real.log (1/η) ∧
      (cc.toQuery (SingleFlagGate.eval a)).vectorQueries=0 ∧
      (cc.workGates : ℝ)≤3328095848*κ*(a+1)*Real.log (1/η) ∧
      cc.CallsOnly (originalSingleFlagPort a (Bits n)) ∧
      ∀ UA Ub (M : Matrix (Bits n) (Bits n) ℂ), M.IsHermitian →
        IsBlockEncoding (fun _ : Fin a=>false) 1 0 UA M →
        IsBlockEncoding (physicalZero a) 1 0 ((cc.toQuery (SingleFlagGate.eval a)).eval UA Ub)
          (Polynomial.aeval M (liftReal (paperCorrectionPolynomial κ η))) := by
  have hp := lemma54_correction_polynomial hκ hη0 hη1
  obtain ⟨cc,hq,hv,hg,hports,he⟩ := lemma24_single_flag_encoding (D := Bits n) (B := Bits n) a
    (paperCorrectionPolynomial κ η) hp.1 (fun x hx=>(hp.2.1 x hx).trans (by norm_num))
  refine ⟨cc,?_,hv,?_,hports,he⟩
  · have hq' : ((cc.toQuery (SingleFlagGate.eval a)).matrixQueries : ℝ)≤4*(paperCorrectionPolynomial κ η).natDegree := by exact_mod_cast hq
    nlinarith [hp.2.2.2]
  · have hg' : (cc.workGates : ℝ)≤15848*((paperCorrectionPolynomial κ η).natDegree+1)*(a+1) := by exact_mod_cast hg
    have hl := kappa_log_ge_one hκ hη0 hη1
    calc
      _ ≤ 15848*(210000*κ*Real.log (1/η)+1)*(a+1) := hg'.trans (by gcongr; exact hp.2.2.2)
      _ ≤ 15848*(210001*(κ*Real.log (1/η)))*(a+1) := by gcongr; nlinarith
      _ = _ := by ring

/-- This data structure carries the actual chosen lists alongside every semantic
and resource fact; later assembly never chooses substitute witnesses. -/
structure Implementation (a n : ℕ) {κ s ŝ ε : ℝ} (h : BudgetParameters κ s ŝ) where
  preparation : CompilerAttachment.Circuit a n (preparationExponent κ)
  filter : GraphAttachedCircuit a (Bits n) (Bits n)
  correction : SingleFlagCircuit a (Bits n) (Bits n)
  preparation_strict : CompilerAttachment.strictCircuit preparation
  preparation_matrix : (preparation.toQuery (CompilerAttachment.gateEval a n _ (CompilerAttachment.preparationExponent_pos h))).matrixQueries=2*mainBudget κ
  preparation_vector : (preparation.toQuery (CompilerAttachment.gateEval a n _ (CompilerAttachment.preparationExponent_pos h))).vectorQueries=2*reflectionBudget κ ŝ+1
  preparation_gates : preparation.workGates≤436789*(a+1)*mainBudget κ+11222*(n+1)*reflectionBudget κ ŝ+2401
  preparation_state : ∀ UA Ub, ((preparation.toQuery (CompilerAttachment.gateEval a n _ (CompilerAttachment.preparationExponent_pos h))).eval UA Ub).val*ᵥ
    Pi.single (CompilerAttachment.allZero a n (preparationExponent κ)) 1=
    basisInsertion (CompilerAttachment.clean a n (preparationExponent κ))*ᵥ
      originalPreparedState (fun _ : Fin a=>false) (fun _ : Fin n=>false) h UA Ub
  filter_matrix : ((filter.toQuery (GraphAttachedGate.eval a)).matrixQueries : ℝ)<96*κ*Real.log (1/(ε/1024))
  filter_vector : (filter.toQuery (GraphAttachedGate.eval a)).vectorQueries=0
  filter_gates : (filter.workGates : ℝ)≤13525928*κ*(a+1)*Real.log (1/(ε/1024))
  filter_ports : filter.CallsOnly (graphOriginalSingleFlagPort a (Bits n))
  filter_block : ∀ UA Ub (M : Matrix (Bits n) (Bits n) ℂ), M.IsHermitian →
    IsBlockEncoding (fun _ : Fin a=>false) 1 0 UA M →
    IsBlockEncoding (physicalZero (a+4)) 1 0 ((filter.toQuery (GraphAttachedGate.eval a)).eval UA Ub)
      (Polynomial.aeval (GraphEncoding.normalizedGraph M κ) (liftReal (kernelFilter (graphFilterGap κ) (ε/1024))))
  correction_matrix : ((correction.toQuery (SingleFlagGate.eval a)).matrixQueries : ℝ)≤840000*κ*Real.log (1/(ε/1024))
  correction_vector : (correction.toQuery (SingleFlagGate.eval a)).vectorQueries=0
  correction_gates : (correction.workGates : ℝ)≤3328095848*κ*(a+1)*Real.log (1/(ε/1024))
  correction_ports : correction.CallsOnly (originalSingleFlagPort a (Bits n))
  correction_block : ∀ UA Ub (M : Matrix (Bits n) (Bits n) ℂ), M.IsHermitian →
    IsBlockEncoding (fun _ : Fin a=>false) 1 0 UA M →
    IsBlockEncoding (physicalZero a) 1 0 ((correction.toQuery (SingleFlagGate.eval a)).eval UA Ub)
      (Polynomial.aeval M (liftReal (paperCorrectionPolynomial κ (ε/1024))))

/-- Every field of the chosen triple is proved from the literal synthesis theorems. -/
theorem implementation_exists (a n : ℕ) {κ s ŝ ε : ℝ} (h : BudgetParameters κ s ŝ)
    (hε0 : 0<ε) (hε1 : ε<1/2) : Nonempty (Implementation a n (ε := ε) h) := by
  have hη0 : 0<ε/1024 := by positivity
  have hη1 : ε/1024<1/2 := by linarith
  obtain ⟨cp,hps,hpm,hpv,hpg,_,hpe⟩ := CompilerAttachment.physical_prepared_state a n h
  obtain ⟨cf,hfm,hfv,hfg,hfp,hfe⟩ := physical_kernel_filter_single_flag
    (D := Bits n) (B := Bits n) a h.kappa_ge_two hη0 hη1
  obtain ⟨cc,hcm,hcv,hcg,hcp,hce⟩ := correction_uniform a n h.kappa_ge_two hη0 hη1
  exact ⟨{
    preparation := cp
    filter := cf
    correction := cc
    preparation_strict := hps
    preparation_matrix := hpm
    preparation_vector := hpv
    preparation_gates := hpg
    preparation_state := hpe
    filter_matrix := hfm
    filter_vector := hfv
    filter_gates := hfg
    filter_ports := hfp
    filter_block := fun UA Ub M hM henc => (hfe UA Ub M hM henc).1
    correction_matrix := hcm
    correction_vector := hcv
    correction_gates := hcg
    correction_ports := hcp
    correction_block := hce }⟩

end OptimalQLS.Refinement.PhysicalProgram
