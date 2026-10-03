import OptimalQLS.LowerBounds.OrdinaryProgramExecution
import OptimalQLS.LowerBounds.ProgramCutDistance

/-! The same genuine cutoff estimate for ordinary success/failure output. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
universe u v
variable {A : Type u} {B : Type v} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  {d w : ℕ}

theorem FiniteOracleProgram.ordinary_truncation_distance (tree : FiniteOracleProgram A B d w)
    (out : Fin d) (q : ℕ) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) :
    traceDistance (tree.ordinaryOutput UA Ub psi) ((tree.truncateVectors out q).ordinaryOutput UA Ub psi) ≤
      tree.cutMass UA Ub q psi := by
  induction tree generalizing q with
  | output success aborted => simp [truncateVectors, cutMass]
  | matrixQuery port adj next ih =>
    rw [truncateVectors, ordinaryOutput_matrixQuery, ordinaryOutput_matrixQuery]
    exact ih q _
  | vectorQuery port adj next ih =>
    cases q with
    | zero =>
      change traceDistance ((FiniteOracleProgram.vectorQuery port adj next).ordinaryOutput UA Ub psi)
        ((FiniteOracleProgram.abortProgram out _).ordinaryOutput UA Ub psi) ≤ bornMass psi
      exact traceDistance_positive_same_trace_le _ _
        ((FiniteOracleProgram.vectorQuery port adj next).ordinaryOutput_positive UA Ub psi)
        ((FiniteOracleProgram.abortProgram out _).ordinaryOutput_positive UA Ub psi) _
        ((FiniteOracleProgram.vectorQuery port adj next).ordinaryOutput_trace UA Ub psi)
        ((FiniteOracleProgram.abortProgram out _).ordinaryOutput_trace UA Ub psi)
    | succ q =>
      rw [truncateVectors, ordinaryOutput_vectorQuery, ordinaryOutput_vectorQuery]
      exact ih q _
  | instrument r dims K hn next ih =>
    rw [truncateVectors, ordinaryOutput_instrument, ordinaryOutput_instrument]
    apply (traceDistance_finset_sum_le Finset.univ _ _).trans
    exact Finset.sum_le_sum (fun i _ => ih i q _)

end OptimalQLS.LowerBounds
