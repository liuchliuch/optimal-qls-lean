import OptimalQLS.LowerBounds.MarkedProgramExecution

/-! The synthetic stopping flag has exactly the recursively computed cut mass. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
universe u v
variable {A : Type u} {B : Type v} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  {d w : ℕ}

def markedAbortProjection : Matrix (Fin d ⊕ (Fin d ⊕ Fin d)) (Fin d ⊕ (Fin d ⊕ Fin d)) ℂ :=
  Matrix.fromBlocks 0 0 0 (Matrix.fromBlocks 0 0 0 1)

theorem markedAbortProjection_norm_le : ‖markedAbortProjection (d := d)‖ ≤ 1 := by
  have hI : ‖(1 : Matrix (Fin d) (Fin d) ℂ)‖ ≤ 1 := QuantumChannelStein.TraceNorm.unitary_opNorm_le_one 1
  simp only [markedAbortProjection, blockDiagonal_norm, norm_zero]
  exact max_le (by norm_num) (max_le (by norm_num) hI)

theorem markedAbortProjection_injection (success aborted : Bool) :
    markedAbortProjection * markedFlagInjection (d := d) success aborted =
      if aborted then markedFlagInjection success aborted else 0 := by
  cases success <;> cases aborted <;>
    simp [markedAbortProjection, markedFlagInjection, Matrix.fromBlocks_mul_fromRows]

theorem markedAbortProjection_conjugation (success aborted : Bool) (X : Matrix (Fin d) (Fin d) ℂ) :
    (markedAbortProjection * (markedFlagInjection success aborted * X * (markedFlagInjection success aborted).conjTranspose)).trace.re =
      if aborted then X.trace.re else 0 := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, markedAbortProjection_injection]
  cases aborted
  · simp
  · simp only [Bool.true_eq, if_true]
    rw [Matrix.trace_mul_cycle, markedFlagInjection_gram, Matrix.one_mul]

def FiniteOracleProgram.abortProbability (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) : ℝ :=
  (markedAbortProjection * tree.markedOutput UA Ub psi).trace.re

theorem FiniteOracleProgram.abortProbability_output (success aborted : Bool)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin d → ℂ) :
    (FiniteOracleProgram.output success aborted).abortProbability UA Ub psi = if aborted then bornMass psi else 0 := by
  rw [abortProbability, markedOutput_output, markedAbortProjection_conjugation, bornMass_eq_trace]

theorem FiniteOracleProgram.abortProbability_instrument (r : ℕ) (dims : Fin r → ℕ)
    (K : ∀ i, Matrix (Fin (dims i)) (Fin w) ℂ) (hn : ∑ i, (K i).conjTranspose * K i = 1)
    (next : ∀ i, FiniteOracleProgram A B d (dims i))
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) :
    (FiniteOracleProgram.instrument r dims K hn next).abortProbability UA Ub psi =
      ∑ i, (next i).abortProbability UA Ub (K i *ᵥ psi) := by
  simp only [abortProbability, markedOutput_instrument, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]

theorem FiniteOracleProgram.abortProbability_abortProgram (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) :
    (FiniteOracleProgram.abortProgram out w).abortProbability UA Ub psi = bornMass psi := by
  rw [abortProgram, abortProbability_instrument]
  simp only [abortProbability_output, Bool.true_eq, if_true]
  exact varying_instrument_bornMass _ _ (abortBasisKraus_normalized out) psi

/-- Ordinary source programs contain no synthetic abort leaves. -/
def FiniteOracleProgram.Clean (tree : FiniteOracleProgram A B d w) : Prop :=
  ∀ k, tree.terminalAbortFlag k = false

/-- This equality identifies the actual abort measurement probability of the
literal truncated circuit with its actual recursively accumulated cut mass. -/
theorem FiniteOracleProgram.truncation_abortProbability (tree : FiniteOracleProgram A B d w)
    (hclean : tree.Clean) (out : Fin d) (q : ℕ)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) :
    (tree.truncateVectors out q).abortProbability UA Ub psi = tree.cutMass UA Ub q psi := by
  induction tree generalizing q with
  | output success aborted =>
    have ha : aborted = false := hclean ()
    simp [truncateVectors, cutMass, abortProbability_output, ha]
  | matrixQuery port adj next ih =>
    unfold truncateVectors
    simp only [abortProbability, markedOutput_matrixQuery]
    exact ih hclean q _
  | vectorQuery port adj next ih =>
    cases q with
    | zero => exact abortProbability_abortProgram out UA Ub psi
    | succ q =>
      unfold truncateVectors
      simp only [abortProbability, markedOutput_vectorQuery]
      exact ih hclean q _
  | instrument r dims K hn next ih =>
    rw [truncateVectors, abortProbability_instrument]
    change (∑ i, ((next i).truncateVectors out q).abortProbability UA Ub (K i *ᵥ psi)) =
      ∑ i, (next i).cutMass UA Ub q (K i *ᵥ psi)
    apply Finset.sum_congr rfl
    intro i _
    exact ih i (fun k => hclean ⟨i, k⟩) q _

end OptimalQLS.LowerBounds
