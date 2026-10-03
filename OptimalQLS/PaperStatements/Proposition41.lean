import OptimalQLS.Preparation.OriginalState
import OptimalQLS.Preparation.CompilerAttachment.Complete

/-! Proposition 4.1: a single strict physical preparation word, selected from
public κ and the supplied estimate, with its exact coarse-state conclusion. -/
noncomputable section
namespace OptimalQLS.PaperStatements
open Matrix TransducerCompiler BinaryClock PolynomialTransform GraphEncoding Alignment
open Preparation Preparation.CompilerAttachment
open scoped Matrix.Norms.L2Operator
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1000000

/-- The implementation is chosen before hidden scales, matrices, prepared
columns and complete original oracles. The semantic state is exactly the
state realized by this same implementation, with three clean scratch bits. -/
theorem proposition41 (a n : ℕ) {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ) :
    ∃ out : Circuit a n (preparationExponent κ),
      (out.toQuery (gateEval a n _ (preparationExponent_pos h))).matrixQueries = 2*mainBudget κ ∧
      (out.toQuery (gateEval a n _ (preparationExponent_pos h))).vectorQueries = 2*reflectionBudget κ ŝ+1 ∧
      (∀ g, NamedInstruction.gate g ∈ out → g.arity ≤ 2 ∧
        ∀ i j, ((gateEval a n _ (preparationExponent_pos h) g).val i j).im = 0) ∧
      (∀ p adj, NamedInstruction.matrixCall p adj ∈ out →
        p = graphSingleFlagPort a n (preparationExponent κ)) ∧
      (∀ p adj, NamedInstruction.vectorCall p adj ∈ out →
        p = sourceSingleFlagPort a n (preparationExponent κ)) ∧
      ∀ (t : ℝ) (ht : BudgetParameters κ t ŝ),
        ((out.toQuery (gateEval a n _ (preparationExponent_pos h))).matrixQueries : ℝ) < 512000000*κ ∧
        ((out.toQuery (gateEval a n _ (preparationExponent_pos h))).vectorQueries : ℝ) < 120000001*(κ/t) ∧
        (out.workGates : ℝ) < 200000000000000*κ*(a+1)+700000000000*(κ/t)*(n+1) ∧
        ∀ (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ),
          let Ψ := originalPreparedState (fun _ : Fin a => false) (fun _ : Fin n => false) ht UA Ub
          ((out.toQuery (gateEval a n _ (preparationExponent_pos h))).eval UA Ub).val *ᵥ
            Pi.single (allZero a n (preparationExponent κ)) 1 =
              basisInsertion (clean a n (preparationExponent κ)) *ᵥ Ψ ∧
          ∀ (A : Matrix (Bits n) (Bits n) ℂ), A.IsHermitian → IsUnit A → ‖Ring.inverse A‖ ≤ κ →
            IsBlockEncoding (fun _ : Fin a => false) 1 0 UA A →
            ∀ (b : EuclideanSpace ℂ (Bits n)), ‖b‖ = 1 →
              (∀ i, Ub i (fun _ : Fin n => false) = b i) → t = solutionScale 1 A b →
              let y := WithLp.toLp 2 (zeroAuxiliaryOutput (physicalSignalZero (fun _ : Fin a => false)) Ψ)
              let H := graphMatrix A κ
              let u := normalizedProjectedInput H (graphInput b)
              ‖WithLp.toLp 2 Ψ‖ = 1 ∧
              ∃ (β : ℝ) (residual : EuclideanSpace ℂ (Fin 4 × Bits n)),
                1/32 ≤ β ∧ β ≤ 1 ∧ y = β • u + residual ∧ kernelProjector H residual = 0 := by
  obtain ⟨out, hm, hv, hg, hr, hmp, hvp, he⟩ := physical_preparation_complete a n h
  refine ⟨out, hm, hv, hr, hmp, hvp, ?_⟩
  intro t ht
  obtain ⟨hgates, hstate⟩ := he t ht
  have hbudgets := originalPreparationAlgorithm_budgets
    (fun _ : Fin a => false) (fun _ : Fin n => false) ht
  rw [(originalPreparationAlgorithm_counts _ _ ht).1,
    (originalPreparationAlgorithm_counts _ _ ht).2] at hbudgets
  refine ⟨?_, ?_, hgates, ?_⟩
  · simpa only [hm] using hbudgets.1
  · simpa only [hv] using hbudgets.2
  intro UA Ub
  refine ⟨hstate UA Ub, ?_⟩
  intro A hA hunit hinv henc b hb hcol hscale
  obtain ⟨hn, β, hβlo, hβhi, hp, hres⟩ := original_preparation_coarse
    (fun _ : Fin a => false) (fun _ : Fin n => false) ht A hA hunit hinv UA henc Ub b hb hcol hscale
  dsimp only at hn hres ⊢
  refine ⟨hn, β, _, hβlo.le, hβhi, ?_, hres⟩
  abel

end OptimalQLS.PaperStatements
