import OptimalQLS.LowerBounds.MarkedProgramExecution

/-! Truncating the actual program costs at most its actual cutoff Born mass. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix QuantumChannelStein.TraceNorm
universe u v
variable {A : Type u} {B : Type v} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  {d w : ℕ}

theorem traceNorm_finset_sum_le {I D : Type*} [Fintype D] [DecidableEq D]
    (s : Finset I) (X : I → Matrix D D ℂ) : traceNorm (∑ i ∈ s, X i) ≤ ∑ i ∈ s, traceNorm (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (traceNorm_add_le _ _).trans (add_le_add_right ih _)

theorem traceDistance_finset_sum_le {I D : Type*} [Fintype D] [DecidableEq D]
    (s : Finset I) (X Y : I → Matrix D D ℂ) :
    traceDistance (∑ i ∈ s, X i) (∑ i ∈ s, Y i) ≤ ∑ i ∈ s, traceDistance (X i) (Y i) := by
  unfold traceDistance
  rw [← Finset.sum_sub_distrib, ← Finset.sum_div]
  exact div_le_div_of_nonneg_right (traceNorm_finset_sum_le s (fun i => X i - Y i)) (by norm_num)

theorem traceDistance_positive_same_trace_le {D : Type*} [Fintype D] [DecidableEq D]
    (X Y : Matrix D D ℂ) (hX : X.PosSemidef) (hY : Y.PosSemidef) (r : ℝ)
    (hXt : X.trace.re = r) (hYt : Y.trace.re = r) : traceDistance X Y ≤ r := by
  simpa using traceDistance_common_positive_residual 0 X Y hX hY r hXt hYt

/-- Exact operational stopping estimate for a single varying-workspace tree.
The cutoff quantity is recursively evaluated Born mass, not a supplied bound. -/
theorem FiniteOracleProgram.truncation_distance (tree : FiniteOracleProgram A B d w)
    (out : Fin d) (q : ℕ) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) :
    traceDistance (tree.markedOutput UA Ub psi) ((tree.truncateVectors out q).markedOutput UA Ub psi) ≤
      tree.cutMass UA Ub q psi := by
  induction tree generalizing q with
  | output success aborted => simp [truncateVectors, cutMass]
  | matrixQuery port adj next ih =>
    rw [truncateVectors, markedOutput_matrixQuery, markedOutput_matrixQuery]
    exact ih q _
  | vectorQuery port adj next ih =>
    cases q with
    | zero =>
      change traceDistance ((FiniteOracleProgram.vectorQuery port adj next).markedOutput UA Ub psi)
        ((FiniteOracleProgram.abortProgram out _).markedOutput UA Ub psi) ≤ bornMass psi
      exact traceDistance_positive_same_trace_le _ _
        ((FiniteOracleProgram.vectorQuery port adj next).markedOutput_positive UA Ub psi)
        ((FiniteOracleProgram.abortProgram out _).markedOutput_positive UA Ub psi) _
        ((FiniteOracleProgram.vectorQuery port adj next).markedOutput_trace UA Ub psi)
        ((FiniteOracleProgram.abortProgram out _).markedOutput_trace UA Ub psi)
    | succ q =>
      rw [truncateVectors, markedOutput_vectorQuery, markedOutput_vectorQuery]
      exact ih q _
  | instrument r dims K hn next ih =>
    rw [truncateVectors, markedOutput_instrument, markedOutput_instrument]
    apply (traceDistance_finset_sum_le Finset.univ _ _).trans
    exact Finset.sum_le_sum (fun i _ => ih i q _)

end OptimalQLS.LowerBounds
