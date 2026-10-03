import OptimalQLS.LowerBounds.FiniteProgramTraceHybrid
import OptimalQLS.LowerBounds.FiniteProgramTruncation
import OptimalQLS.LowerBounds.HaltingInstrument

/-! Recursive execution laws for the ordinary success/failure program channel. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
universe u v
variable {A : Type u} {B : Type v} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  {d w : ℕ}

def FiniteOracleProgram.ordinaryOutput (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) :
    Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ :=
  (tree.outputChannel UA Ub).apply (pureDensity psi)

theorem FiniteOracleProgram.ordinaryOutput_output (success aborted : Bool)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin d → ℂ) :
    (FiniteOracleProgram.output success aborted).ordinaryOutput UA Ub psi =
      flagInjection success * pureDensity psi * (flagInjection success).conjTranspose := by
  simp [ordinaryOutput, outputChannel, FiniteChannel.ofKraus_apply, outputKraus,
    Terminal, terminalKraus, terminalSuccess, terminalAbortFlag]

theorem FiniteOracleProgram.ordinaryOutput_matrixQuery (port : OptimalQLS.QueryPort A (Fin w)) (adj : Bool)
    (next : FiniteOracleProgram A B d w) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) :
    (FiniteOracleProgram.matrixQuery port adj next).ordinaryOutput UA Ub psi =
      next.ordinaryOutput UA Ub ((port.apply (if adj then UA⁻¹ else UA) : Matrix (Fin w) (Fin w) ℂ) *ᵥ psi) := by
  simp only [ordinaryOutput, outputChannel, FiniteChannel.ofKraus_apply, outputKraus,
    terminalKraus, terminalSuccess, terminalAbortFlag, pureDensity_mulVec, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rfl

theorem FiniteOracleProgram.ordinaryOutput_vectorQuery (port : OptimalQLS.QueryPort B (Fin w)) (adj : Bool)
    (next : FiniteOracleProgram A B d w) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) :
    (FiniteOracleProgram.vectorQuery port adj next).ordinaryOutput UA Ub psi =
      next.ordinaryOutput UA Ub ((port.apply (if adj then Ub⁻¹ else Ub) : Matrix (Fin w) (Fin w) ℂ) *ᵥ psi) := by
  simp only [ordinaryOutput, outputChannel, FiniteChannel.ofKraus_apply, outputKraus,
    terminalKraus, terminalSuccess, terminalAbortFlag, pureDensity_mulVec, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rfl

theorem FiniteOracleProgram.ordinaryOutput_instrument (r : ℕ) (dims : Fin r → ℕ)
    (K : ∀ i, Matrix (Fin (dims i)) (Fin w) ℂ) (hn : ∑ i, (K i).conjTranspose * K i = 1)
    (next : ∀ i, FiniteOracleProgram A B d (dims i))
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) :
    (FiniteOracleProgram.instrument r dims K hn next).ordinaryOutput UA Ub psi =
      ∑ i, (next i).ordinaryOutput UA Ub (K i *ᵥ psi) := by
  simp only [ordinaryOutput, outputChannel, FiniteChannel.ofKraus_apply]
  change (∑ k : (i : Fin r) × (next i).Terminal, _) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  simp only [outputKraus, terminalKraus, terminalSuccess, terminalAbortFlag,
    pureDensity_mulVec, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem FiniteOracleProgram.ordinaryOutput_positive (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) :
    (tree.ordinaryOutput UA Ub psi).PosSemidef :=
  (tree.outputChannel UA Ub).apply_positive (pureDensity_positive psi)

theorem FiniteOracleProgram.ordinaryOutput_trace (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) :
    (tree.ordinaryOutput UA Ub psi).trace.re = bornMass psi := by
  rw [ordinaryOutput, FiniteChannel.trace_apply, bornMass_eq_trace]

end OptimalQLS.LowerBounds
