import OptimalQLS.LowerBounds.CanonicalLowerFacts
import OptimalQLS.LowerBounds.SameInstanceLowerBound

/-! Same-instance lower bounds on conventional Fin/zero-input QLS oracles. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
universe r

def QuantumProgram.CorrectHermitianQLS {d : ℕ} [NeZero d] {Node : ℕ → Type r} {w : ℕ}
    (p : OptimalQLS.QLSParameters)
    (program : QuantumProgram (OptimalQLS.SignalIndex p.signalQubits × Fin d) (Fin d) d Node)
    (out : Fin d) (node : Node w) (psi : Fin w → ℂ) : Prop :=
  ∀ (M : Matrix (Fin d) (Fin d) ℂ) (b : OptimalQLS.DataSpace d)
    (UA : Matrix.unitaryGroup (OptimalQLS.SignalIndex p.signalQubits × Fin d) ℂ)
    (Ub : Matrix.unitaryGroup (Fin d) ℂ),
    M.IsHermitian → OptimalQLS.ExactQLSPromise p M b UA Ub →
      program.Solves out UA Ub node psi (fun i => OptimalQLS.normalizedSolution M b i) p.epsilon

theorem QuantumProgram.canonical_pointwise_vector_lower_bound {N m : ℕ} [NeZero N]
    {kappa estimate eps : ℝ} (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) {Node : ℕ → Type r} {w : ℕ}
    (program : QuantumProgram (OptimalQLS.SignalIndex 1 × Fin (hardOutputDimension N))
      (Fin (hardOutputDimension N)) (hardOutputDimension N) Node)
    (out : Fin (hardOutputDimension N)) (node : Node w) (psi : Fin w → ℂ) (hpsi : ‖WithLp.toLp 2 psi‖ = 1)
    (hsolve : program.Solves out (canonicalHardEncoding (N := N) hk z) (canonicalHardPreparation hk he hek hN)
      node psi (canonicalSolution N kappa estimate z) eps)
    (hsolve' : program.Solves out (canonicalHardEncoding (N := N) hk z) (canonicalPerturbedPreparation hk he hek hN)
      node psi (canonicalPairedSolution N kappa estimate z) eps)
    (heps : eps ≤ 1 / 64) (q : ℕ)
    (hq : program.PointwiseVectorBound out (canonicalHardEncoding (N := N) hk z) (canonicalHardPreparation hk he hek hN) node psi q) :
    kappa / (75 * estimate) ≤ (q : ℝ) := by
  let UA := canonicalHardEncoding (N := N) hk z
  let U := canonicalHardPreparation hk he hek hN
  let V := canonicalPerturbedPreparation hk he hek hN
  let T := ketBra (canonicalDirection N) (canonicalDirection N)
  have hp := program.successProbability_bounds out UA U node psi hpsi
  have hp' := program.successProbability_bounds out UA V node psi hpsi
  have hpos : 0 < program.successProbability out UA U node psi := by linarith [hsolve.1]
  have hpos' : 0 < program.successProbability out UA V node psi := by linarith [hsolve'.1]
  have hsep := flagged_solver_outputs_separated T (pureDensity (canonicalSolution N kappa estimate z))
    (pureDensity (canonicalPairedSolution N kappa estimate z))
    (program.conditionalOutput out UA U node psi) (program.conditionalOutput out UA V node psi)
    (program.failureDensity out UA U node psi) (program.failureDensity out UA V node psi)
    (program.successProbability out UA U node psi) (program.successProbability out UA V node psi) eps
    (ketBra_self_norm_le_one _ (canonicalDirection_norm N)) (canonical_original_direction_probability hk z)
    (canonical_paired_direction_probability hk he hek hN z) hp.1 hp.2 hsolve'.1 hp'.2 hsolve.2 hsolve'.2 heps
  rw [← program.totalOutput_flagged out UA U node psi hpos, ← program.totalOutput_flagged out UA V node psi hpos'] at hsep
  have hhybrid := program.one_sided_vector_hybrid out UA U V node psi hpsi q hq
  have hd := canonical_preparation_distance hk he hek hN
  have hbound := hsep.trans (hhybrid.trans (mul_le_mul_of_nonneg_left hd (by positivity)))
  have hbound' : (1 / 10 : ℝ) ≤ (15 * (q : ℝ) * estimate) / (2 * kappa) := by convert hbound using 1 <;> ring
  have h := (le_div_iff₀ (show 0 < 2 * kappa by linarith)).mp hbound'
  apply (div_le_iff₀ (show 0 < 75 * estimate by positivity)).mpr
  nlinarith

/-- Correctness on every promised Hermitian input is specialized to the actual
original and paired inputs through literal ExactQLSPromise proofs. -/
theorem QuantumProgram.canonical_same_instance_lower_bound
    {N m : ℕ} [NeZero N] [NeZero m] {kappa estimate eps : ℝ}
    (hk : 8 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (heps : 0 < eps) (hsmall : eps ≤ Real.exp (-16))
    (hm : m = logarithmicParityLength kappa eps)
    (hN : N = 2 * historyPadding kappa + 2 * m) {Node : ℕ → Type r} {w : ℕ}
    (program : QuantumProgram (OptimalQLS.SignalIndex 1 × Fin (hardOutputDimension N))
      (Fin (hardOutputDimension N)) (hardOutputDimension N) Node)
    (out : Fin (hardOutputDimension N)) (node : Node w) (psi : Fin w → ℂ) (hpsi : ‖WithLp.toLp 2 psi‖ = 1)
    (hcorrect : program.CorrectHermitianQLS (canonicalLowerParameters kappa estimate eps) out node psi) :
    ∃ z : BitString m,
      OptimalQLS.ExactQLSPromise (canonicalLowerParameters kappa estimate eps)
        (canonicalHardMatrix N kappa z) (canonicalHardSource N m kappa estimate)
        (canonicalHardEncoding (N := N) (show 4 ≤ kappa by linarith) z)
        (canonicalHardPreparation (show 4 ≤ kappa by linarith) he hek hN) ∧
      EntrywiseReal (canonicalHardMatrix N kappa z) ∧ (canonicalHardMatrix N kappa z).IsHermitian ∧
      ‖canonicalHardMatrix N kappa z‖ = 1 ∧ ‖Ring.inverse (canonicalHardMatrix N kappa z)‖ = kappa ∧
      (hardOutputDimension N : ℝ) ≤ 9 * kappa * Real.log (1 / eps) ∧
      (∀ qA : ℕ, program.PointwiseMatrixBound out
        (canonicalHardEncoding (N := N) (show 4 ≤ kappa by linarith) z)
        (canonicalHardPreparation (show 4 ≤ kappa by linarith) he hek hN) node psi qA →
        kappa * Real.log (1 / eps) / 192 ≤ (qA : ℝ)) ∧
      (∀ qB : ℕ, program.PointwiseVectorBound out
        (canonicalHardEncoding (N := N) (show 4 ≤ kappa by linarith) z)
        (canonicalHardPreparation (show 4 ≤ kappa by linarith) he hek hN) node psi qB →
        kappa / (75 * estimate) ≤ (qB : ℝ)) := by
  have hk4 : 4 ≤ kappa := by linarith
  have hepsUpper : eps < 1 / 2 := lt_of_le_of_lt (logarithmic_accuracy_vector_small hsmall) (by norm_num)
  have hsolve (z : BitString m) : program.Solves out (canonicalHardEncoding (N := N) hk4 z)
      (canonicalHardPreparation hk4 he hek hN) node psi (canonicalSolution N kappa estimate z) eps := by
    have h := hcorrect (canonicalHardMatrix N kappa z) (canonicalHardSource N m kappa estimate)
      (canonicalHardEncoding hk4 z) (canonicalHardPreparation hk4 he hek hN) (canonicalHardMatrix_hermitian kappa z)
      (canonicalHard_ExactQLSPromise hk4 he hek heps hepsUpper hN z)
    rw [canonicalSolution_normalizedSolution hk4 he hek hN z] at h
    exact h
  have hsolve' (z : BitString m) : program.Solves out (canonicalHardEncoding (N := N) hk4 z)
      (canonicalPerturbedPreparation hk4 he hek hN) node psi (canonicalPairedSolution N kappa estimate z) eps := by
    have h := hcorrect (canonicalHardMatrix N kappa z) (canonicalPerturbedSource N m kappa estimate)
      (canonicalHardEncoding hk4 z) (canonicalPerturbedPreparation hk4 he hek hN) (canonicalHardMatrix_hermitian kappa z)
      (canonicalPerturbed_ExactQLSPromise hk4 he hek heps hepsUpper hN z)
    rw [canonicalPairedSolution_normalizedSolution hk4 he z] at h
    exact h
  have hgap : 2 * eps < (5 / 2304 : ℝ) * historyLambda kappa ^ (2 * m) := by
    have h := logarithmic_signal_strict hk heps hsmall
    rw [← hm] at h
    linarith
  obtain ⟨z, fuel, k, hborn, hqueries⟩ := program.matrix_hard_run_of_solver out
    (canonicalHardPolynomial hk4 hN) (canonicalHardPolynomial_degree hk4 hN)
    (fun z => canonicalHardEncoding (N := N) hk4 z) (canonicalHardPreparation hk4 he hek hN)
    (canonicalHardPolynomial_eval hk4 hN) node psi hpsi (canonicalSolution N kappa estimate)
    (canonicalWeight hk4 hN) (canonicalWeight_bound hk4 hN) hgap hsolve (fun z => canonical_signal hk4 he hek hN z)
  refine ⟨z, canonicalHard_ExactQLSPromise hk4 he hek heps hepsUpper hN z,
    canonicalHardMatrix_real kappa z, canonicalHardMatrix_hermitian kappa z,
    canonicalHardMatrix_norm hk4 hN z, canonicalHardMatrix_inverse_norm hk4 z, ?_, ?_, ?_⟩
  · have hNlog : N = logarithmicHistorySize kappa eps := by simp only [logarithmicHistorySize, ← hm, hN]
    rw [hardOutputDimension, hNlog]
    exact logarithmicHardFamily_dimension_upper hk heps hsmall
  · intro qA hqA
    have hq := hqA fuel k hborn
    have hnat : m ≤ 2 * qA := hqueries.trans (Nat.mul_le_mul_left 2 hq)
    have hreal : (m : ℝ) ≤ 2 * (qA : ℝ) := by exact_mod_cast hnat
    have hmlower := (logarithmicParityLength_bounds hk heps hsmall).2.1
    rw [← hm] at hmlower
    linarith
  · intro qB hqB
    exact program.canonical_pointwise_vector_lower_bound hk4 he hek hN z out node psi hpsi
      (hsolve z) (hsolve' z) (logarithmic_accuracy_vector_small hsmall) qB hqB

end OptimalQLS.LowerBounds
