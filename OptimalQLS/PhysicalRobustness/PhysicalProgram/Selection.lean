import OptimalQLS.PhysicalRobustness.CoherentRefinement
import OptimalQLS.PhysicalRobustness.Preparation
import OptimalQLS.Refinement.PhysicalProgram.Complete

/-! Fixed physical noisy-program witnesses, selected only from classical inputs. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open scoped Classical Matrix.Norms.L2Operator
namespace OptimalQLS.PhysicalRobustness.PhysicalProgram
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform PhysicalPadding

/-- A purely classical budget witness at K=2κ and supplied estimate 9ŝ/8. -/
def selectionBudget {κ ŝ : ℝ} (hκ : 2≤κ) (hlo : 1/2≤ŝ) (hhi : ŝ≤2*κ) :
    BudgetParameters (2*κ) (knownScaleWitness (2*κ) (9*ŝ/8)) (9*ŝ/8) :=
  knownScaleWitness_budget (by linarith) (by linarith) (by linarith)

/-- The same three lists provide semantics and all resource bounds. The scale
appearing in correctness is universally quantified, and never selects code. -/
structure Implementation (a n : ℕ) (κ ŝ ε : ℝ) where
  kappa_ge_two : 2≤κ
  estimate_lower : 1/2≤ŝ
  estimate_upper : ŝ≤2*κ
  preparation : CompilerAttachment.Circuit a n (preparationExponent (2*κ))
  filter : GraphAttachedCircuit a (Bits n) (Bits n)
  correction : SingleFlagCircuit a (Bits n) (Bits n)
  preparation_strict : CompilerAttachment.strictCircuit preparation
  preparation_matrix : (preparation.toQuery (CompilerAttachment.gateEval a n _
    (CompilerAttachment.preparationExponent_pos (selectionBudget kappa_ge_two estimate_lower estimate_upper)))).matrixQueries=2*mainBudget (2*κ)
  preparation_vector : (preparation.toQuery (CompilerAttachment.gateEval a n _
    (CompilerAttachment.preparationExponent_pos (selectionBudget kappa_ge_two estimate_lower estimate_upper)))).vectorQueries=2*reflectionBudget (2*κ) (9*ŝ/8)+1
  preparation_gates : preparation.workGates≤436789*(a+1)*mainBudget (2*κ)+11222*(n+1)*reflectionBudget (2*κ) (9*ŝ/8)+2401
  preparation_state : ∀ (t : ℝ) (h : BudgetParameters (2*κ) t (9*ŝ/8)) UA Ub,
    ((preparation.toQuery (CompilerAttachment.gateEval a n _ (CompilerAttachment.preparationExponent_pos h))).eval UA Ub).val*ᵥ
      Pi.single (CompilerAttachment.allZero a n (preparationExponent (2*κ))) 1=
      basisInsertion (CompilerAttachment.clean a n (preparationExponent (2*κ)))*ᵥ
        originalPreparedState (fun _ : Fin a=>false) (fun _ : Fin n=>false) h UA Ub
  filter_matrix : ((filter.toQuery (GraphAttachedGate.eval a)).matrixQueries : ℝ)<192*κ*Real.log (1/(ε/4096))
  filter_vector : (filter.toQuery (GraphAttachedGate.eval a)).vectorQueries=0
  filter_gates : (filter.workGates : ℝ)≤27051856*κ*(a+1)*Real.log (1/(ε/4096))
  filter_ports : filter.CallsOnly (graphOriginalSingleFlagPort a (Bits n))
  filter_semantics : ∀ UA Ub (B : Matrix (Bits n) (Bits n) ℂ), B.IsHermitian →
    IsBlockEncoding (fun _ : Fin a=>false) 1 0 UA B →
    IsBlockEncoding (physicalZero (a+4)) 1 0 ((filter.toQuery (GraphAttachedGate.eval a)).eval UA Ub)
      (Polynomial.aeval (GraphEncoding.normalizedGraph B (2*κ)) (liftReal (kernelFilter (graphFilterGap (2*κ)) (ε/4096)))) ∧
    ‖Matrix.toEuclideanCLM (n := Fin 4 × Bits n) (𝕜 := ℂ)
      (signalBlock (physicalZero (a+4)) ((filter.toQuery (GraphAttachedGate.eval a)).eval UA Ub))-
      Alignment.kernelProjector (GraphEncoding.graphMatrix B (2*κ))‖≤ε/4096
  correction_matrix : ((correction.toQuery (SingleFlagGate.eval a)).matrixQueries : ℝ)≤34004000000*κ*Real.log (1/(ε/4096))
  correction_vector : (correction.toQuery (SingleFlagGate.eval a)).vectorQueries=0
  correction_gates : (correction.workGates : ℝ)≤150000000000000*κ*(a+1)*Real.log (1/(ε/4096))
  correction_ports : correction.CallsOnly (originalSingleFlagPort a (Bits n))
  correction_block : ∀ UA Ub (B : Matrix (Bits n) (Bits n) ℂ), B.IsHermitian →
    IsBlockEncoding (fun _ : Fin a=>false) 1 0 UA B →
    IsBlockEncoding (physicalZero a) 1 0 ((correction.toQuery (SingleFlagGate.eval a)).eval UA Ub)
      (Polynomial.aeval B (liftReal (noisyCorrectionPolynomial κ (ε/4096))))

/-- Literal synthesis precedes the embedding, matrices, source and complete oracles. -/
theorem implementation_exists (a n : ℕ) {κ ŝ ε : ℝ}
    (hκ : 2≤κ) (hlo : 1/2≤ŝ) (hhi : ŝ≤2*κ) (hε : 0<ε) (hε1 : ε<1/2) :
    Nonempty (Implementation a n κ ŝ ε) := by
  let h := selectionBudget hκ hlo hhi
  have heta : 0<ε/4096 := by positivity
  have heta1 : ε/4096<1/2 := by linarith
  obtain ⟨cp,hps,hpm,hpv,hpg,_,hpe⟩ := CompilerAttachment.physical_prepared_state a n h
  obtain ⟨cf,hfm,hfv,hfg,hfp,hfe⟩ := physical_kernel_filter_single_flag
    (D := Bits n) (B := Bits n) a (κ := 2*κ) (by linarith) heta heta1
  obtain ⟨cc,hcm,hcv,hcg,hcp,hce⟩ := noisyCorrection_single_flag
    (D := Bits n) (W := Bits n) a hκ heta heta1
  refine ⟨{
    kappa_ge_two := hκ
    estimate_lower := hlo
    estimate_upper := hhi
    preparation := cp
    filter := cf
    correction := cc
    preparation_strict := hps
    preparation_matrix := hpm
    preparation_vector := hpv
    preparation_gates := hpg
    preparation_state := ?_
    filter_matrix := by nlinarith
    filter_vector := hfv
    filter_gates := by nlinarith
    filter_ports := hfp
    filter_semantics := hfe
    correction_matrix := hcm
    correction_vector := hcv
    correction_gates := hcg
    correction_ports := hcp
    correction_block := hce }⟩
  intro t h' UA Ub
  rw [←CompilerAttachment.originalPreparedState_uniform a n h h' UA Ub]
  exact hpe UA Ub

end OptimalQLS.PhysicalRobustness.PhysicalProgram
