import OptimalQLS.LowerBounds.QuantumOutputLimit
import OptimalQLS.LowerBounds.ProgramSolverGuarantee
import OptimalQLS.LowerBounds.SuccessEventSeparation

/-! Heralded correctness evaluated on the actual unbounded program output. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
namespace OptimalQLS.LowerBounds
open Matrix Filter
universe u v r
variable {A : Type u} {B : Type v} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  {d w : ℕ} {Node : ℕ → Type r}

theorem matrix_entry_zero_of_limit {D E : Type*} [Fintype D] [Fintype E]
    (X : ℕ → Matrix D E ℂ) (Y : Matrix D E ℂ) (hlim : Tendsto X atTop (𝓝 Y))
    (i : D) (j : E) (hz : ∀ n, X n i j = 0) : Y i j = 0 := by
  have hc : Continuous (fun M : Matrix D E ℂ => M i j) := by fun_prop
  have h := (hc.tendsto Y).comp hlim
  have heq : (fun n => X n i j) = fun _ : ℕ => (0 : ℂ) := funext hz
  change Tendsto (fun n => X n i j) atTop _ at h
  rw [heq] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

def QuantumProgram.successDensity (program : QuantumProgram A B d Node) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (node : Node w) (psi : Fin w → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  (program.totalOutput out UA Ub node psi).submatrix Sum.inl Sum.inl

def QuantumProgram.failureDensity (program : QuantumProgram A B d Node) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (node : Node w) (psi : Fin w → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  (program.totalOutput out UA Ub node psi).submatrix Sum.inr Sum.inr

theorem QuantumProgram.totalOutput_blocks (program : QuantumProgram A B d Node) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (node : Node w) (psi : Fin w → ℂ) :
    program.totalOutput out UA Ub node psi =
      Matrix.fromBlocks (program.successDensity out UA Ub node psi) 0 0 (program.failureDensity out UA Ub node psi) := by
  ext (i | i) (j | j)
  · rfl
  · change (program.totalOutput out UA Ub node psi) (.inl i) (.inr j) = 0
    apply matrix_entry_zero_of_limit _ _ (program.totalOutput_tendsto out UA Ub node psi)
    intro n
    rw [FiniteOracleProgram.ordinaryOutput, FiniteOracleProgram.outputChannel_pureDensity]
    rfl
  · change (program.totalOutput out UA Ub node psi) (.inr i) (.inl j) = 0
    apply matrix_entry_zero_of_limit _ _ (program.totalOutput_tendsto out UA Ub node psi)
    intro n
    rw [FiniteOracleProgram.ordinaryOutput, FiniteOracleProgram.outputChannel_pureDensity]
    rfl
  · rfl

def QuantumProgram.successProbability (program : QuantumProgram A B d Node) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (node : Node w) (psi : Fin w → ℂ) : ℝ :=
  (program.successDensity out UA Ub node psi).trace.re

def QuantumProgram.conditionalOutput (program : QuantumProgram A B d Node) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (node : Node w) (psi : Fin w → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  (program.successProbability out UA Ub node psi)⁻¹ • program.successDensity out UA Ub node psi

/-- The solver guarantee uses actual success probability and conditional
state of the proved output limit. Nontermination already counts as failure. -/
def QuantumProgram.Solves (program : QuantumProgram A B d Node) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (node : Node w) (psi : Fin w → ℂ)
    (target : Fin d → ℂ) (eps : ℝ) : Prop :=
  2 / 3 ≤ program.successProbability out UA Ub node psi ∧
    traceDistance (program.conditionalOutput out UA Ub node psi) (pureDensity target) ≤ eps

theorem QuantumProgram.successProbability_bounds (program : QuantumProgram A B d Node) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (node : Node w) (psi : Fin w → ℂ)
    (hpsi : ‖WithLp.toLp 2 psi‖ = 1) :
    0 ≤ program.successProbability out UA Ub node psi ∧ program.successProbability out UA Ub node psi ≤ 1 := by
  have hs := ((program.totalOutput_positive out UA Ub node psi).submatrix Sum.inl).trace_nonneg.1
  have hf := ((program.totalOutput_positive out UA Ub node psi).submatrix Sum.inr).trace_nonneg.1
  have hm := congrArg Complex.re (program.totalOutput_trace out UA Ub node psi)
  rw [program.totalOutput_blocks, trace_blockDiagonal, bornMass_eq_norm_sq, hpsi] at hm
  simp only [Complex.add_re, Complex.ofReal_re, one_pow] at hm
  norm_num at hs hf
  change 0 ≤ (program.successDensity out UA Ub node psi).trace.re at hs
  change 0 ≤ (program.failureDensity out UA Ub node psi).trace.re at hf
  change 0 ≤ (program.successDensity out UA Ub node psi).trace.re ∧ _
  exact ⟨hs, by dsimp only [successProbability]; linarith⟩

theorem QuantumProgram.successDensity_eq_probability_smul (program : QuantumProgram A B d Node) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (node : Node w) (psi : Fin w → ℂ)
    (hp : 0 < program.successProbability out UA Ub node psi) :
    program.successDensity out UA Ub node psi = program.successProbability out UA Ub node psi •
      program.conditionalOutput out UA Ub node psi := by
  rw [conditionalOutput, smul_smul, mul_inv_cancel₀ hp.ne', one_smul]

theorem QuantumProgram.totalOutput_flagged (program : QuantumProgram A B d Node) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (node : Node w) (psi : Fin w → ℂ)
    (hp : 0 < program.successProbability out UA Ub node psi) :
    program.totalOutput out UA Ub node psi = flaggedOutput (program.successProbability out UA Ub node psi)
      (program.conditionalOutput out UA Ub node psi) (program.failureDensity out UA Ub node psi) := by
  rw [program.totalOutput_blocks, program.successDensity_eq_probability_smul out UA Ub node psi hp]
  rfl

theorem QuantumProgram.successObservable_trace (program : QuantumProgram A B d Node) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (node : Node w) (psi : Fin w → ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ) :
    (successObservable T * program.totalOutput out UA Ub node psi).trace.re =
      (T * program.successDensity out UA Ub node psi).trace.re := by
  rw [program.totalOutput_blocks, successObservable, Matrix.fromBlocks_multiply]
  simp [trace_blockDiagonal]

theorem FiniteOracleProgram.successObservable_trace (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) (T : Matrix (Fin d) (Fin d) ℂ) :
    (successObservable T * tree.ordinaryOutput UA Ub psi).trace.re = (T * tree.executeDensity UA Ub id psi).trace.re := by
  rw [ordinaryOutput, tree.outputChannel_pureDensity, successObservable, Matrix.fromBlocks_multiply]
  simp [trace_blockDiagonal]

theorem QuantumProgram.success_signed_expectation_positive {m : ℕ}
    (program : QuantumProgram A B d Node) (out : Fin d) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (node : Node w) (psi : Fin w → ℂ) (target : Fin d → ℂ) (T : Matrix (Fin d) (Fin d) ℂ)
    (z : BitString m) {eps signal : ℝ} (hsolve : program.Solves out UA Ub node psi target eps)
    (hT : ‖T‖ ≤ 1) (hsignal : signal ≤ paritySign z * (T * pureDensity target).trace.re)
    (hgap : 2 * eps < signal) :
    0 < paritySign z * (successObservable T * program.totalOutput out UA Ub node psi).trace.re := by
  have hp : 0 < program.successProbability out UA Ub node psi := by linarith [hsolve.1]
  have hcond := parity_expectation_preserved z T _ _ hT hsolve.2 hsignal hgap
  rw [program.totalOutput_flagged out UA Ub node psi hp, successObservable_expectation]
  nlinarith [mul_pos hp hcond]

end OptimalQLS.LowerBounds
