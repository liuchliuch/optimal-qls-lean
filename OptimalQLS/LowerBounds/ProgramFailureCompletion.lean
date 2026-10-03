import OptimalQLS.LowerBounds.QuantumCompleted
import OptimalQLS.LowerBounds.OrdinaryProgramExecution

/-! Literal failure state used for fuel exhaustion and nontermination. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
universe u v r
variable {A : Type u} {B : Type v} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  {d w : ℕ} {Node : ℕ → Type r}

theorem pureDensity_complex_smul {D : Type*} [Fintype D] [DecidableEq D]
    (c : ℂ) (v : D → ℂ) : pureDensity (c • v) = Complex.normSq c • pureDensity v := by
  ext i j
  simp only [pureDensity, ketBra, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Pi.star_apply, StarMul.star_mul, Matrix.smul_apply, RCLike.real_smul_eq_coe_mul]
  change c * v i * (star (v j) * star c) = (Complex.normSq c : ℂ) * (v i * star (v j))
  rw [Complex.normSq_eq_conj_mul_self]
  change c * v i * (star (v j) * star c) = (star c * c) * (v i * star (v j))
  ring

def outputBasisVector (out : Fin d) : Fin d → ℂ := Pi.single out 1

@[simp] theorem outputBasisVector_norm (out : Fin d) : ‖WithLp.toLp 2 (outputBasisVector out)‖ = 1 := by
  simp [outputBasisVector]

theorem abortBasisKraus_mulVec (out : Fin d) (j : Fin w) (psi : Fin w → ℂ) :
    abortBasisKraus out j *ᵥ psi = psi j • outputBasisVector out := by
  ext i
  by_cases hi : i = out
  · subst i
    simp [abortBasisKraus, outputBasisVector, Matrix.mulVec, dotProduct]
  · simp [abortBasisKraus, outputBasisVector, Matrix.mulVec, dotProduct, hi, Ne.symm hi]

def ordinaryFailureState (out : Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ :=
  flagInjection false * pureDensity (outputBasisVector out) * (flagInjection false).conjTranspose

theorem ordinaryFailureState_positive (out : Fin d) : (ordinaryFailureState out).PosSemidef :=
  (pureDensity_positive _).mul_mul_conjTranspose_same _

@[simp] theorem ordinaryFailureState_trace (out : Fin d) : (ordinaryFailureState out).trace = 1 := by
  rw [ordinaryFailureState, Matrix.trace_mul_cycle, flagInjection_gram, Matrix.one_mul, pureDensity_trace, outputBasisVector_norm]
  norm_num

theorem FiniteOracleProgram.abortProgram_ordinaryOutput (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) :
    (FiniteOracleProgram.abortProgram out w).ordinaryOutput UA Ub psi = bornMass psi • ordinaryFailureState out := by
  rw [abortProgram, ordinaryOutput_instrument]
  simp only [ordinaryOutput_output, abortBasisKraus_mulVec, pureDensity_complex_smul,
    Matrix.mul_smul, Matrix.smul_mul, ← Finset.sum_smul]
  rfl

/-- Every actual fuel prefix equals its completed quantum output plus its
remaining Born mass in one fixed ordinary-failure state. -/
theorem QuantumProgram.unroll_output_decomposition (program : QuantumProgram A B d Node) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (fuel : ℕ) (node : Node w) (psi : Fin w → ℂ) :
    (program.unroll out fuel node).ordinaryOutput UA Ub psi = program.completedPrefix out UA Ub node psi fuel +
      (bornMass psi - (program.completedPrefix out UA Ub node psi fuel).trace.re) • ordinaryFailureState out := by
  induction fuel generalizing w with
  | zero => simp [completedPrefix, unroll, FiniteOracleProgram.abortProgram_ordinaryOutput]
  | succ fuel ih =>
    simp only [unroll, completedPrefix]
    cases program.step node with
    | output success =>
      rw [FiniteOracleProgram.ordinaryOutput_output]
      simp only [FiniteOracleProgram.completedDensity, Bool.false_eq_true, if_false]
      rw [Matrix.trace_mul_cycle, flagInjection_gram, Matrix.one_mul, ← bornMass_eq_trace]
      simp
    | matrixQuery port adj next =>
      rw [FiniteOracleProgram.ordinaryOutput_matrixQuery]
      simp only [FiniteOracleProgram.completedDensity]
      rw [ih next, unitary_bornMass]
      rfl
    | vectorQuery port adj next =>
      rw [FiniteOracleProgram.ordinaryOutput_vectorQuery]
      simp only [FiniteOracleProgram.completedDensity]
      rw [ih next, unitary_bornMass]
      rfl
    | instrument rank dims K hn next =>
      rw [FiniteOracleProgram.ordinaryOutput_instrument]
      simp only [FiniteOracleProgram.completedDensity]
      simp_rw [ih]
      rw [Finset.sum_add_distrib, ← Finset.sum_smul, Finset.sum_sub_distrib,
        varying_instrument_bornMass dims K hn psi, Matrix.trace_sum, Complex.re_sum]
      rfl

end OptimalQLS.LowerBounds
