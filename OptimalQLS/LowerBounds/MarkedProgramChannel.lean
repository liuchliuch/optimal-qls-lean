import OptimalQLS.LowerBounds.FiniteProgramChannel
import OptimalQLS.LowerBounds.FiniteProgramHybrid

/-! A literal three-flag channel keeps truncation aborts separate from failure. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix QuantumChannelStein.TraceNorm
universe u v
variable {A : Type u} {B : Type v} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  {d w : ℕ}

def markedFlagInjection (success aborted : Bool) : Matrix (Fin d ⊕ (Fin d ⊕ Fin d)) (Fin d) ℂ :=
  if aborted then Matrix.fromRows 0 (Matrix.fromRows 0 1)
  else if success then Matrix.fromRows 1 0 else Matrix.fromRows 0 (Matrix.fromRows 1 0)

theorem markedFlagInjection_gram (success aborted : Bool) :
    (markedFlagInjection (d := d) success aborted).conjTranspose * markedFlagInjection (d := d) success aborted = 1 := by
  cases success <;> cases aborted <;> simp [markedFlagInjection,
    Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromRows]

def FiniteOracleProgram.markedReadoutKraus (tree : FiniteOracleProgram A B d w) :
    tree.Terminal → Matrix (Fin d ⊕ (Fin d ⊕ Fin d)) (tree.Terminal × Fin d) ℂ := by
  classical
  exact fun k => markedFlagInjection (tree.terminalSuccess k) (tree.terminalAbortFlag k) * terminalProjection k

theorem FiniteOracleProgram.markedReadoutKraus_normalized (tree : FiniteOracleProgram A B d w) :
    (∑ k, (tree.markedReadoutKraus k).conjTranspose * tree.markedReadoutKraus k) = 1 := by
  classical
  calc
    _ = ∑ k : tree.Terminal, (terminalProjection k).conjTranspose * terminalProjection (d := d) k := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [markedReadoutKraus, Matrix.conjTranspose_mul]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (markedFlagInjection (tree.terminalSuccess k) (tree.terminalAbortFlag k)).conjTranspose,
        markedFlagInjection_gram, Matrix.one_mul]
    _ = 1 := terminalProjection_normalized

def FiniteOracleProgram.markedReadoutChannel (tree : FiniteOracleProgram A B d w) :
    FiniteChannel (tree.Terminal × Fin d) (Fin d ⊕ (Fin d ⊕ Fin d)) := by
  classical
  exact FiniteChannel.ofKraus tree.markedReadoutKraus tree.markedReadoutKraus_normalized

def FiniteOracleProgram.markedOutputKraus (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (k : tree.Terminal) :
    Matrix (Fin d ⊕ (Fin d ⊕ Fin d)) (Fin w) ℂ := markedFlagInjection (tree.terminalSuccess k) (tree.terminalAbortFlag k) * tree.terminalKraus UA Ub k

theorem FiniteOracleProgram.markedOutputKraus_normalized (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (∑ k, (tree.markedOutputKraus UA Ub k).conjTranspose * tree.markedOutputKraus UA Ub k) = 1 := by
  calc
    _ = ∑ k, (tree.terminalKraus UA Ub k).conjTranspose * tree.terminalKraus UA Ub k := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [markedOutputKraus, Matrix.conjTranspose_mul]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (markedFlagInjection (tree.terminalSuccess k) (tree.terminalAbortFlag k)).conjTranspose,
        markedFlagInjection_gram, Matrix.one_mul]
    _ = 1 := tree.terminalKraus_normalized UA Ub

def FiniteOracleProgram.markedOutputChannel (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) : FiniteChannel (Fin w) (Fin d ⊕ (Fin d ⊕ Fin d)) :=
  FiniteChannel.ofKraus (tree.markedOutputKraus UA Ub) (tree.markedOutputKraus_normalized UA Ub)

theorem FiniteOracleProgram.project_markedTerminalIsometry (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (k : tree.Terminal) :
    tree.markedReadoutKraus k * tree.terminalIsometry UA Ub = tree.markedOutputKraus UA Ub k := by
  classical
  have hp : terminalProjection k * tree.terminalIsometry UA Ub = tree.terminalKraus UA Ub k := by
    ext i j
    simp [terminalProjection, terminalIsometry, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [markedReadoutKraus, Matrix.mul_assoc, hp]
  rfl

/-- Actual channel output equals the fixed readout applied to the actual
terminal Stinespring matrix, for every input density matrix. -/
theorem FiniteOracleProgram.markedOutputChannel_stinespring (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (X : Matrix (Fin w) (Fin w) ℂ) :
    (tree.markedOutputChannel UA Ub).apply X = tree.markedReadoutChannel.apply
      (tree.terminalIsometry UA Ub * X * (tree.terminalIsometry UA Ub).conjTranspose) := by
  classical
  rw [markedOutputChannel, markedReadoutChannel, FiniteChannel.ofKraus_apply, FiniteChannel.ofKraus_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [← tree.project_markedTerminalIsometry UA Ub k, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]


theorem FiniteOracleProgram.markedOutputChannel_vector_hybrid (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (U V : Matrix.unitaryGroup B ℂ)
    (rho : Matrix (Fin w) (Fin w) ℂ) (hpositive : rho.PosSemidef) (hmass : rho.trace = 1) :
    traceDistance ((tree.markedOutputChannel UA U).apply rho) ((tree.markedOutputChannel UA V).apply rho) ≤
      (tree.vectorDepth : ℝ) * ‖(U : Matrix B B ℂ) - (V : Matrix B B ℂ)‖ := by
  rw [tree.markedOutputChannel_stinespring, tree.markedOutputChannel_stinespring]
  apply (tree.markedReadoutChannel.traceDistance_contract _ _).trans
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
