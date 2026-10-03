import OptimalQLS.PhysicalPadding.SpectralGap
import OptimalQLS.PolynomialTransform.SingleFlagPaperTheorems

/-!
# Single-flag kernel filtering for singular physical data operators

This is the existing physical single-flag circuit and its existing counts.
Only the spectral argument is strengthened: the global physical graph filter
works for every Hermitian data block encoded by the supplied oracle, including
literal zero-padding, with no data inverse or replacement oracle.
-/

noncomputable section
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace OptimalQLS.PhysicalPadding

open Matrix Polynomial PolynomialTransform DirtyAncilla
open scoped Matrix.Norms.L2Operator

variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

/-- The actual single-flag graph-filter circuit, uniformly for every Hermitian
exactly encoded data operator, without invertibility or inverse-norm premises.
The approximation is in global operator norm against the actual graph kernel. -/
theorem physical_kernel_filter_single_flag [Nonempty D] (a : ℕ)
    {κ η : ℝ} (hκ : 2 ≤ κ) (hη0 : 0 < η) (hη1 : η < 1 / 2) :
    ∃ out : GraphAttachedCircuit a D B,
      ((out.toQuery (GraphAttachedGate.eval a)).matrixQueries : ℝ) <
        96 * κ * Real.log (1 / η) ∧
      (out.toQuery (GraphAttachedGate.eval a)).vectorQueries = 0 ∧
      (out.workGates : ℝ) ≤ 13525928 * κ * (a + 1) * Real.log (1 / η) ∧
      out.CallsOnly (graphOriginalSingleFlagPort a D) ∧
      ∀ (U : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ)
        (Ub : Matrix.unitaryGroup B ℂ) (A : Matrix D D ℂ),
        A.IsHermitian → IsBlockEncoding (fun _ : Fin a => false) 1 0 U A →
        IsBlockEncoding (physicalZero (a + 4)) 1 0
          ((out.toQuery (GraphAttachedGate.eval a)).eval U Ub)
          (Polynomial.aeval (GraphEncoding.normalizedGraph A κ)
            (liftReal (kernelFilter (graphFilterGap κ) η))) ∧
        ‖Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ)
            (signalBlock (physicalZero (a + 4))
              ((out.toQuery (GraphAttachedGate.eval a)).eval U Ub)) -
          (LinearMap.ker (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ)
            (GraphEncoding.graphMatrix A κ)).toLinearMap).starProjection‖ ≤ η := by
  have hk : 0 < κ := by linarith
  have hd : 0 < graphFilterGap κ ∧ graphFilterGap κ ≤ 1 / Real.sqrt 12 :=
    ⟨graphFilterGap_pos hk, min_le_right _ _⟩
  have hp := lemma51_kernel_filter hd.1 hd.2 hη0 hη1
  have hdeg := paperGraphFilter_degree_bound hκ hη0 hη1
  obtain ⟨out, hm, hv, hg, hports, henc⟩ := graphPolynomial_single_flag (D := D) (B := B)
    a κ hk (kernelFilter (graphFilterGap κ) η) hp.1 hp.2.2.2.1
  refine ⟨out, ?_, hv, ?_, hports, ?_⟩
  · have hm' : ((out.toQuery (GraphAttachedGate.eval a)).matrixQueries : ℝ) ≤
        8 * (kernelFilter (graphFilterGap κ) η).natDegree := by exact_mod_cast hm
    nlinarith
  · have hg' : (out.workGates : ℝ) ≤
        (6248 * (a + 5) + 1009216) *
          ((kernelFilter (graphFilterGap κ) η).natDegree + 1) := by exact_mod_cast hg
    refine (hg'.trans ?_).trans (single_flag_graph_gate_bound a hκ hη0 hη1)
    gcongr
  · intro U Ub A hA hU
    have he := henc U Ub A hA hU
    refine ⟨he, ?_⟩
    have heq := exact_block_eq he
    rw [one_smul] at heq
    rw [← heq, polynomial_matrix_to_operator, ← normalizedGraph_kernel_projection A hk]
    have hs : (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ)
        (GraphEncoding.normalizedGraph A κ)).toLinearMap.IsSymmetric :=
      Matrix.isHermitian_iff_isSymmetric.mp (GraphEncoding.normalizedGraph_hermitian A hA κ)
    apply kernelFilter_operator_bound _ hs hd.1 hd.2 hη0 hη1
    intro μ hmem hμ
    obtain ⟨hlo, hup⟩ := normalized_graph_spectrum_singular_safe A hA hκ
      (norm_le_of_exact_block hU) μ hmem hμ
    refine ⟨(min_le_left _ _).trans ?_, hup⟩
    simpa only [graphNormalization] using hlo

end OptimalQLS.PhysicalPadding
