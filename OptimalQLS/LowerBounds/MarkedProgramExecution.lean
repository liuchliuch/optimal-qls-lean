import OptimalQLS.LowerBounds.MarkedProgramChannel
import OptimalQLS.LowerBounds.FiniteProgramTruncation
import OptimalQLS.LowerBounds.HaltingInstrument

/-! Recursive execution laws for the exact three-flag program channel. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
universe u v
variable {A : Type u} {B : Type v} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  {d w : ℕ}

def FiniteOracleProgram.markedOutput (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) :
    Matrix (Fin d ⊕ (Fin d ⊕ Fin d)) (Fin d ⊕ (Fin d ⊕ Fin d)) ℂ :=
  (tree.markedOutputChannel UA Ub).apply (pureDensity psi)

theorem FiniteOracleProgram.markedOutput_output (success aborted : Bool)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin d → ℂ) :
    (FiniteOracleProgram.output success aborted).markedOutput UA Ub psi =
      markedFlagInjection success aborted * pureDensity psi * (markedFlagInjection success aborted).conjTranspose := by
  simp [markedOutput, markedOutputChannel, FiniteChannel.ofKraus_apply, markedOutputKraus,
    Terminal, terminalKraus, terminalSuccess, terminalAbortFlag]

theorem FiniteOracleProgram.markedOutput_matrixQuery (port : OptimalQLS.QueryPort A (Fin w)) (adj : Bool)
    (next : FiniteOracleProgram A B d w) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) :
    (FiniteOracleProgram.matrixQuery port adj next).markedOutput UA Ub psi =
      next.markedOutput UA Ub ((port.apply (if adj then UA⁻¹ else UA) : Matrix (Fin w) (Fin w) ℂ) *ᵥ psi) := by
  simp only [markedOutput, markedOutputChannel, FiniteChannel.ofKraus_apply, markedOutputKraus,
    terminalKraus, terminalSuccess, terminalAbortFlag, pureDensity_mulVec, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rfl

theorem FiniteOracleProgram.markedOutput_vectorQuery (port : OptimalQLS.QueryPort B (Fin w)) (adj : Bool)
    (next : FiniteOracleProgram A B d w) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) :
    (FiniteOracleProgram.vectorQuery port adj next).markedOutput UA Ub psi =
      next.markedOutput UA Ub ((port.apply (if adj then Ub⁻¹ else Ub) : Matrix (Fin w) (Fin w) ℂ) *ᵥ psi) := by
  simp only [markedOutput, markedOutputChannel, FiniteChannel.ofKraus_apply, markedOutputKraus,
    terminalKraus, terminalSuccess, terminalAbortFlag, pureDensity_mulVec, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rfl

theorem FiniteOracleProgram.markedOutput_instrument (r : ℕ) (dims : Fin r → ℕ)
    (K : ∀ i, Matrix (Fin (dims i)) (Fin w) ℂ) (hn : ∑ i, (K i).conjTranspose * K i = 1)
    (next : ∀ i, FiniteOracleProgram A B d (dims i))
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) :
    (FiniteOracleProgram.instrument r dims K hn next).markedOutput UA Ub psi =
      ∑ i, (next i).markedOutput UA Ub (K i *ᵥ psi) := by
  simp only [markedOutput, markedOutputChannel, FiniteChannel.ofKraus_apply]
  change (∑ k : (i : Fin r) × (next i).Terminal, _) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  simp only [markedOutputKraus, terminalKraus, terminalSuccess, terminalAbortFlag,
    pureDensity_mulVec, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem FiniteOracleProgram.markedOutput_positive (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) :
    (tree.markedOutput UA Ub psi).PosSemidef :=
  (tree.markedOutputChannel UA Ub).apply_positive (pureDensity_positive psi)

theorem FiniteOracleProgram.markedOutput_trace (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) :
    (tree.markedOutput UA Ub psi).trace.re = bornMass psi := by
  rw [markedOutput, FiniteChannel.trace_apply, bornMass_eq_trace]

end OptimalQLS.LowerBounds
