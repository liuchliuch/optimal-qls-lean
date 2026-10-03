import OptimalQLS.LowerBounds.ProgramDiagonalDecoder
import OptimalQLS.LowerBounds.TraceDistance

/-! Solver correctness is expressed on the common program's actual outputs. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
universe u v
variable {A : Type u} {B : Type v} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  {d w : ℕ}

/-- Ordinary heralded correctness, evaluated on actual recursively executed
success probability and conditional density matrix. -/
def FiniteOracleProgram.Solves (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ)
    (target : Fin d → ℂ) (eps : ℝ) : Prop :=
  2 / 3 ≤ tree.successProbability UA Ub psi ∧
    traceDistance (tree.conditionalOutput UA Ub psi) (pureDensity target) ≤ eps

theorem paritySign_abs {m : ℕ} (z : BitString m) : |paritySign z| = 1 := by
  rw [← boolSign_xorFold_ofFn z]
  cases xorFold (List.ofFn z) <;> norm_num [boolSign]

theorem parity_expectation_preserved {D : Type*} [Fintype D] [DecidableEq D] {m : ℕ}
    (z : BitString m) (T rho target : Matrix D D ℂ) {eps signal : ℝ}
    (hT : ‖T‖ ≤ 1) (herr : traceDistance rho target ≤ eps)
    (hsignal : signal ≤ paritySign z * (T * target).trace.re) (hgap : 2 * eps < signal) :
    0 < paritySign z * (T * rho).trace.re := by
  have h := bounded_observable_difference T rho target hT
  have hdiff : |paritySign z * (T * rho).trace.re - paritySign z * (T * target).trace.re| ≤ 2 * eps := by
    rw [← mul_sub, abs_mul, paritySign_abs, one_mul]
    exact h.trans (by linarith)
  have hneg := neg_abs_le (paritySign z * (T * rho).trace.re - paritySign z * (T * target).trace.re)
  linarith

theorem FiniteOracleProgram.success_signed_expectation_positive {m : ℕ}
    (tree : FiniteOracleProgram A B d w) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (psi : Fin w → ℂ) (target : Fin d → ℂ) (T : Matrix (Fin d) (Fin d) ℂ)
    (z : BitString m) {eps signal : ℝ} (hsolve : tree.Solves UA Ub psi target eps)
    (hT : ‖T‖ ≤ 1) (hsignal : signal ≤ paritySign z * (T * pureDensity target).trace.re)
    (hgap : 2 * eps < signal) :
    0 < paritySign z * (T * tree.executeDensity UA Ub id psi).trace.re := by
  have hp : 0 < tree.successProbability UA Ub psi := by linarith [hsolve.1]
  have hcond := parity_expectation_preserved z T _ _ hT hsolve.2 hsignal hgap
  rw [tree.successDensity_eq_probability_smul UA Ub psi hp, Matrix.mul_smul, Matrix.trace_smul]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  nlinarith [mul_pos hp hcond]

/-- No separately assumed parity bias: actual solver accuracy and the fixed
observable signal suffice for the same-program polynomial reduction. -/
theorem FiniteOracleProgram.matrix_hard_run_of_solver {m : ℕ}
    (tree : FiniteOracleProgram A B d w) (P : Matrix A A (InputPolynomial m)) (hdegree : MatrixDegreeLE P 1)
    (UA : BitString m → Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (heval : ∀ z, evalMatrix z P = (UA z : Matrix A A ℂ))
    (psi : Fin w → ℂ) (hpsi : ‖WithLp.toLp 2 psi‖ = 1)
    (target : BitString m → Fin d → ℂ) (weights : Fin d → ℝ) (hw : ∀ i, |weights i| ≤ 1)
    {eps signal : ℝ} (hgap : 2 * eps < signal)
    (hsolve : ∀ z, tree.Solves (UA z) Ub psi (target z) eps)
    (hsignal : ∀ z, signal ≤ paritySign z *
      (Matrix.diagonal (fun i => (weights i : ℂ)) * pureDensity (target z)).trace.re) :
    ∃ (z : BitString m) (k : tree.Terminal),
      0 < (tree.terminalPath (.initial psi) k).bornWeight (UA z) Ub ∧
        m ≤ 2 * (tree.terminalPath (.initial psi) k).matrixQueries := by
  have hT : ‖Matrix.diagonal (fun i => (weights i : ℂ))‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    simpa using hw i
  exact tree.diagonal_decoder_matrix_hard_run P hdegree UA Ub heval psi hpsi weights hw
    (fun z => tree.success_signed_expectation_positive (UA z) Ub psi (target z) _ z (hsolve z) hT (hsignal z) hgap)

end OptimalQLS.LowerBounds
