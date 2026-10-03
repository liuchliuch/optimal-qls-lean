import OptimalQLS.PolynomialTransform.GraphPolynomial
import OptimalQLS.GraphEncoding.ControlledCircuit
import OptimalQLS.PolynomialTransform.ParameterBounds

/-! # Polynomial-transformation endpoints in the concrete QueryPort model

All polynomial, phase, graph, control-work, and scratch implementations are
proved. QueryPort permits an explicit finite control predicate as one oracle
call. Normalizing its constant-size mask to a strictly single-control oracle
primitive is a separate final model-strengthening adapter. -/
noncomputable section
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000
namespace OptimalQLS.PolynomialTransform
open Matrix Polynomial DirtyAncilla
open scoped Matrix.Norms.L2Operator
variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

/-- Lemma5.2 in the concrete QueryPort model, with the manuscript's exact
minimum-defined δ, actual
original-matrix oracle calls, physically local elementary gate lists, a+9
signal qubits, and distance to the actual graph kernel projection. All
polynomial, phase, graph, control, scratch, and synthesis premises are proved. -/
theorem lemma52_kernel_filter [Nonempty D] (a : ℕ)
    {κ η : ℝ} (hκ : 2 ≤ κ) (hη0 : 0 < η) (hη1 : η < 1/2) :
    ∃ out : GraphAttachedCircuit a D B,
      ((out.toQuery (GraphAttachedGate.eval a)).matrixQueries : ℝ) < 96*κ*Real.log (1/η) ∧
      (out.toQuery (GraphAttachedGate.eval a)).vectorQueries=0 ∧
      (out.workGates : ℝ) ≤ 13107848*κ*(a+1)*Real.log (1/η) ∧
      ∀ (U : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ)
        (A : Matrix D D ℂ), A.IsHermitian → IsUnit A →
        IsBlockEncoding (fun _ : Fin a => false) 1 0 U A → ‖Ring.inverse A‖ ≤ κ →
        IsBlockEncoding (physicalZero (a+4)) 1 0 ((out.toQuery (GraphAttachedGate.eval a)).eval U Ub)
          (Polynomial.aeval (GraphEncoding.normalizedGraph A κ) (liftReal (kernelFilter (graphFilterGap κ) η))) ∧
        ‖Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ)
            (signalBlock (physicalZero (a+4)) ((out.toQuery (GraphAttachedGate.eval a)).eval U Ub))-
          (LinearMap.ker (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ)
            (GraphEncoding.graphMatrix A κ)).toLinearMap).starProjection‖ ≤ η := by
  have hk : 0 < κ := by linarith
  choose calls hm hv hg he using
    (fun mask => GraphEncoding.controlled_graph_elementary (S := Fin a → Bool) (D := D) (B := B) κ hk mask)
  obtain ⟨out,houtq,houtv,houtg,houte⟩ := graphKernel_from_masked_calls a hκ hη0 hη1
    244264 calls (fun mask => ⟨hm mask,hv mask⟩) hg he
  refine ⟨out,houtq,houtv,?_,houte⟩
  apply (show (out.workGates : ℝ) ≤ (6248*(a+5)+977056)*(12*κ*Real.log (1/η)+1) by
    norm_num at houtg ⊢
    exact houtg).trans
  exact graph_gate_bound_linear a hκ hη0 hη1

/-- Lemma5.5 in the concrete QueryPort model, with an explicit constant
multiplying the paper's work-gate bound. -/
theorem lemma55_correction [Nonempty D] (a : ℕ)
    {κ η : ℝ} (hκ : 2 ≤ κ) (hη0 : 0 < η) (hη1 : η < 1/2) :
    ∃ c : ElementaryCircuit ((Fin a → Bool) × D) B (QSVTWire a) D,
      (c.toQuery.matrixQueries : ℝ) ≤ 840000*κ*Real.log (1/η) ∧ c.toQuery.vectorQueries=0 ∧
      (c.workGates : ℝ) ≤ 1312086248*κ*(a+1)*Real.log (1/η) ∧
      ∀ (U : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ)
        (A : Matrix D D ℂ), A.IsHermitian → IsUnit A →
        IsBlockEncoding (fun _ : Fin a => false) 1 0 U A → ‖Ring.inverse A‖ ≤ κ →
        IsBlockEncoding (physicalZero a) 1 0 (c.toQuery.eval U Ub)
          (Polynomial.aeval A (liftReal (paperCorrectionPolynomial κ η))) ∧
        ‖signalBlock (physicalZero a) (c.toQuery.eval U Ub)-
          (1/4 : ℂ) • (1+((κ⁻¹)^2 : ℂ) • (Ring.inverse A)^2)‖ ≤ η/2 := by
  obtain ⟨c,hq,hv,hg,he⟩ := lemma55_correction_elementary_circuit (D := D) (B := B) a hκ hη0 hη1
  exact ⟨c,hq,hv,hg.trans (correction_gate_bound_linear a hκ hη0 hη1),he⟩

end OptimalQLS.PolynomialTransform
