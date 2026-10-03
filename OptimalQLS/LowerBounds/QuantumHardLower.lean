import OptimalQLS.LowerBounds.QuantumSolverGuarantee
import OptimalQLS.LowerBounds.HardFamilyDecoder

/-!
# Both lower-bound reductions in one unbounded quantum-program semantics

The matrix reduction uses an actual common finite prefix whose successful
observable sign is positive on every input. The vector reduction uses the
proved one-sided stopping hybrid of that very instruction coalgebra.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace OptimalQLS.LowerBounds
open Matrix Filter
universe u v r
variable {A : Type u} {B : Type v} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  {d w : ℕ} {Node : ℕ → Type r}

def QuantumProgram.PointwiseMatrixBound (program : QuantumProgram A B d Node) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (node : Node w) (psi : Fin w → ℂ) (q : ℕ) : Prop :=
  ∀ fuel, ∀ k : (program.unroll out fuel node).Terminal,
    0 < ((program.unroll out fuel node).terminalPath (.initial psi) k).bornWeight UA Ub →
      ((program.unroll out fuel node).terminalPath (.initial psi) k).matrixQueries ≤ q

/-- Actual solver correctness selects a genuinely reachable matrix-hard run
of an actual finite prefix, hence of the unbounded program. -/
theorem QuantumProgram.matrix_hard_run_of_solver {m : ℕ}
    (program : QuantumProgram A B d Node) (out : Fin d)
    (P : Matrix A A (InputPolynomial m)) (hdegree : MatrixDegreeLE P 1)
    (UA : BitString m → Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (heval : ∀ z, evalMatrix z P = (UA z : Matrix A A ℂ))
    (node : Node w) (psi : Fin w → ℂ) (hpsi : ‖WithLp.toLp 2 psi‖ = 1)
    (target : BitString m → Fin d → ℂ) (weights : Fin d → ℝ) (hw : ∀ i, |weights i| ≤ 1)
    {eps signal : ℝ} (hgap : 2 * eps < signal)
    (hsolve : ∀ z, program.Solves out (UA z) Ub node psi (target z) eps)
    (hsignal : ∀ z, signal ≤ paritySign z *
      (Matrix.diagonal (fun i => (weights i : ℂ)) * pureDensity (target z)).trace.re) :
    ∃ (z : BitString m) (fuel : ℕ) (k : (program.unroll out fuel node).Terminal),
      0 < ((program.unroll out fuel node).terminalPath (.initial psi) k).bornWeight (UA z) Ub ∧
        m ≤ 2 * ((program.unroll out fuel node).terminalPath (.initial psi) k).matrixQueries := by
  let T : Matrix (Fin d) (Fin d) ℂ := Matrix.diagonal (fun i => (weights i : ℂ))
  have hT : ‖T‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    simpa using hw i
  have hpos (z : BitString m) : 0 < paritySign z * (successObservable T * program.totalOutput out (UA z) Ub node psi).trace.re :=
    program.success_signed_expectation_positive out (UA z) Ub node psi (target z) T z (hsolve z) hT (hsignal z) hgap
  have hc : Continuous (fun X : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ => (successObservable T * X).trace.re) :=
    Complex.continuous_re.comp (matrixTrace_continuous.comp (continuous_const.mul continuous_id))
  have hevent (z : BitString m) : ∀ᶠ fuel in atTop,
      0 < paritySign z * (successObservable T * (program.unroll out fuel node).ordinaryOutput (UA z) Ub psi).trace.re := by
    have ht := ((hc.tendsto (program.totalOutput out (UA z) Ub node psi)).comp
      (program.totalOutput_tendsto out (UA z) Ub node psi)).const_mul (paritySign z)
    exact ht.eventually (lt_mem_nhds (hpos z))
  obtain ⟨fuel, hfuel⟩ := (eventually_all.mpr hevent).exists
  obtain ⟨z, k, hborn, hqueries⟩ := (program.unroll out fuel node).diagonal_decoder_matrix_hard_run
    P hdegree UA Ub heval psi hpsi weights hw (fun z => by
      have h := hfuel z
      rw [FiniteOracleProgram.successObservable_trace] at h
      exact h)
  exact ⟨z, fuel, k, hborn, hqueries⟩

theorem QuantumProgram.hard_family_matrix_hard_run {N m : ℕ} [NeZero N] [NeZero m]
    {kappa estimate eps : ℝ} (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) {Node : ℕ → Type r} {w : ℕ}
    (program : QuantumProgram (Bool × HardFamilyIndex N) (HardFamilyIndex N) (hardOutputDimension N) Node)
    (out : Fin (hardOutputDimension N)) (node : Node w) (psi : Fin w → ℂ) (hpsi : ‖WithLp.toLp 2 psi‖ = 1)
    (hgap : 2 * eps < (5 / 2304 : ℝ) * historyLambda kappa ^ (2 * m))
    (hsolve : ∀ z : BitString m, program.Solves out (hardFamilyEncoding (N := N) hk z) (hardFamilyPreparation hk he hek hN)
      node psi (hardOutputSolution N kappa estimate z) eps) :
    ∃ (z : BitString m) (fuel : ℕ) (k : (program.unroll out fuel node).Terminal),
      0 < ((program.unroll out fuel node).terminalPath (.initial psi) k).bornWeight
        (hardFamilyEncoding (N := N) hk z) (hardFamilyPreparation hk he hek hN) ∧
        m ≤ 2 * ((program.unroll out fuel node).terminalPath (.initial psi) k).matrixQueries :=
  program.matrix_hard_run_of_solver out (hardFamilyPolynomial hk hN) (hardFamilyPolynomial_degree hk hN)
    (fun z => hardFamilyEncoding (N := N) hk z) (hardFamilyPreparation hk he hek hN)
    (hardFamilyPolynomial_eval hk hN) node psi hpsi (hardOutputSolution N kappa estimate)
    (hardOutputWeight hk hN) (hardOutputWeight_bound hk hN) hgap hsolve (fun z => hardOutput_signal hk he hek hN z)

/-- Pointwise vector hardness on every original family member in the actual
unbounded, branch-dependent finite-workspace instruction semantics. -/
theorem QuantumProgram.hard_family_pointwise_vector_lower_bound {N m : ℕ} [NeZero N]
    {kappa estimate eps : ℝ} (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) {Node : ℕ → Type r} {w : ℕ}
    (program : QuantumProgram (Bool × HardFamilyIndex N) (HardFamilyIndex N) (hardOutputDimension N) Node)
    (out : Fin (hardOutputDimension N)) (node : Node w) (psi : Fin w → ℂ) (hpsi : ‖WithLp.toLp 2 psi‖ = 1)
    (hsolve : program.Solves out (hardFamilyEncoding (N := N) hk z) (hardFamilyPreparation hk he hek hN)
      node psi (hardOutputSolution N kappa estimate z) eps)
    (hsolve' : program.Solves out (hardFamilyEncoding (N := N) hk z) (hardFamilyPerturbedPreparation hk he hek hN)
      node psi (hardOutputPairedSolution N kappa estimate z) eps)
    (heps : eps ≤ 1 / 64) (q : ℕ)
    (hq : program.PointwiseVectorBound out (hardFamilyEncoding (N := N) hk z) (hardFamilyPreparation hk he hek hN) node psi q) :
    kappa / (75 * estimate) ≤ (q : ℝ) := by
  let UA := hardFamilyEncoding (N := N) hk z
  let U := hardFamilyPreparation hk he hek hN
  let V := hardFamilyPerturbedPreparation hk he hek hN
  let T := ketBra (hardOutputDirection N) (hardOutputDirection N)
  have hp := program.successProbability_bounds out UA U node psi hpsi
  have hp' := program.successProbability_bounds out UA V node psi hpsi
  have hpos : 0 < program.successProbability out UA U node psi := by linarith [hsolve.1]
  have hpos' : 0 < program.successProbability out UA V node psi := by linarith [hsolve'.1]
  have hsep := flagged_solver_outputs_separated T (pureDensity (hardOutputSolution N kappa estimate z))
    (pureDensity (hardOutputPairedSolution N kappa estimate z))
    (program.conditionalOutput out UA U node psi) (program.conditionalOutput out UA V node psi)
    (program.failureDensity out UA U node psi) (program.failureDensity out UA V node psi)
    (program.successProbability out UA U node psi) (program.successProbability out UA V node psi) eps
    (ketBra_self_norm_le_one _ (hardOutputDirection_norm N)) (hardOutput_original_direction_probability hk z)
    (hardOutput_paired_direction_probability hk he hek hN z) hp.1 hp.2 hsolve'.1 hp'.2 hsolve.2 hsolve'.2 heps
  rw [← program.totalOutput_flagged out UA U node psi hpos, ← program.totalOutput_flagged out UA V node psi hpos'] at hsep
  have hhybrid := program.one_sided_vector_hybrid out UA U V node psi hpsi q hq
  have hd : ‖(U : Matrix (HardFamilyIndex N) (HardFamilyIndex N) ℂ) - (V : Matrix (HardFamilyIndex N) (HardFamilyIndex N) ℂ)‖ ≤ 5 * estimate / (2 * kappa) := by
    rw [norm_sub_rev]
    exact hardFamilyPerturbedPreparation_distance hk he hek hN
  have hbound := hsep.trans (hhybrid.trans (mul_le_mul_of_nonneg_left hd (by positivity)))
  have hbound' : (1 / 10 : ℝ) ≤ (15 * (q : ℝ) * estimate) / (2 * kappa) := by convert hbound using 1 <;> ring
  have h := (le_div_iff₀ (show 0 < 2 * kappa by linarith)).mp hbound'
  apply (div_le_iff₀ (show 0 < 75 * estimate by positivity)).mpr
  nlinarith

end OptimalQLS.LowerBounds
