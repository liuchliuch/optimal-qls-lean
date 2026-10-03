import OptimalQLS.LowerBounds.FiniteProgramHybrid
import OptimalQLS.LowerBounds.FiniteProgramDensity

/-! Genuine trace-distance hybrid for the common varying-workspace program. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix QuantumChannelStein.TraceNorm
universe u v
variable {A : Type u} {B : Type v} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  {d w : ℕ}

theorem FiniteOracleProgram.outputChannel_vector_hybrid (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (U V : Matrix.unitaryGroup B ℂ)
    (rho : Matrix (Fin w) (Fin w) ℂ) (hpositive : rho.PosSemidef) (hmass : rho.trace = 1) :
    traceDistance ((tree.outputChannel UA U).apply rho) ((tree.outputChannel UA V).apply rho) ≤
      (tree.vectorDepth : ℝ) * ‖(U : Matrix B B ℂ) - (V : Matrix B B ℂ)‖ := by
  rw [tree.outputChannel_stinespring, tree.outputChannel_stinespring]
  apply (tree.readoutChannel.traceDistance_contract _ _).trans
  have h := traceNorm_dilation_difference_le (tree.terminalIsometry UA U) (tree.terminalIsometry UA V) rho
  rw [traceNorm_positive_eq_trace rho hpositive, hmass] at h
  simp only [Complex.one_re, mul_one] at h
  have hU := tree.terminalIsometry_norm_le_one UA U
  have hV := tree.terminalIsometry_norm_le_one UA V
  have hdiff := norm_nonneg (tree.terminalIsometry UA U - tree.terminalIsometry UA V)
  have hn := tree.terminalIsometry_vector_hybrid UA U V
  unfold traceDistance
  nlinarith

end OptimalQLS.LowerBounds
