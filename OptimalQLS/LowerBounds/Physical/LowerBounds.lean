import OptimalQLS.LowerBounds.Physical.HardFamily

/-! Same-instance lower bounds on complete physical qubit-register oracles. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix PhysicalPadding Physical
universe r

/-- Correctness for all supplied whole physical unitaries, including arbitrary
choices on off-signal and unused-data columns. The target uses the logical
invertible matrix and the fixed computational zero-inclusion. -/
def QuantumProgram.CorrectHermitianPhysicalQLS {d : ℕ} [NeZero d] {Node : ℕ → Type r} {w : ℕ}
    (p : OptimalQLS.QLSParameters)
    (program : QuantumProgram (OptimalQLS.SignalIndex p.signalQubits × Fin (physicalDimension d))
      (Fin (physicalDimension d)) (physicalDimension d) Node)
    (out : Fin (physicalDimension d)) (node : Node w) (psi : Fin w → ℂ) : Prop :=
  ∀ (M : Matrix (Fin d) (Fin d) ℂ) (b : OptimalQLS.DataSpace d)
    (UA : Matrix.unitaryGroup (OptimalQLS.SignalIndex p.signalQubits × Fin (physicalDimension d)) ℂ)
    (Ub : Matrix.unitaryGroup (Fin (physicalDimension d)) ℂ),
    M.IsHermitian → PhysicalExactQLSPromise p M b UA Ub →
      program.Solves out UA Ub node psi (fun i => physicalSolution M b i) p.epsilon

theorem QuantumProgram.physical_pointwise_vector_lower_bound {N m : ℕ} [NeZero N]
    {kappa estimate eps : ℝ} (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) {Node : ℕ → Type r} {w : ℕ}
    (program : QuantumProgram (OptimalQLS.SignalIndex 1 × Fin (paddedDimension N))
      (Fin (paddedDimension N)) (paddedDimension N) Node)
    (out : Fin (paddedDimension N)) (node : Node w) (psi : Fin w → ℂ) (hpsi : ‖WithLp.toLp 2 psi‖ = 1)
    (hsolve : program.Solves out (paddedEncoding (N := N) hk z) (paddedPreparation hk he hek hN)
      node psi (paddedSolution N kappa estimate z) eps)
    (hsolve' : program.Solves out (paddedEncoding (N := N) hk z) (paddedPerturbedPreparation hk he hek hN)
      node psi (paddedPairedSolution N kappa estimate z) eps)
    (heps : eps ≤ 1 / 64) (q : ℕ)
    (hq : program.PointwiseVectorBound out (paddedEncoding (N := N) hk z) (paddedPreparation hk he hek hN) node psi q) :
    kappa / (75 * estimate) ≤ (q : ℝ) := by
  let UA := paddedEncoding (N := N) hk z
  let U := paddedPreparation hk he hek hN
  let V := paddedPerturbedPreparation hk he hek hN
  let T := ketBra (paddedDirection N) (paddedDirection N)
  have hp := program.successProbability_bounds out UA U node psi hpsi
  have hp' := program.successProbability_bounds out UA V node psi hpsi
  have hpos : 0 < program.successProbability out UA U node psi := by linarith [hsolve.1]
  have hpos' : 0 < program.successProbability out UA V node psi := by linarith [hsolve'.1]
  have hsep := flagged_solver_outputs_separated T (pureDensity (paddedSolution N kappa estimate z))
    (pureDensity (paddedPairedSolution N kappa estimate z))
    (program.conditionalOutput out UA U node psi) (program.conditionalOutput out UA V node psi)
    (program.failureDensity out UA U node psi) (program.failureDensity out UA V node psi)
    (program.successProbability out UA U node psi) (program.successProbability out UA V node psi) eps
    (ketBra_self_norm_le_one _ (paddedDirection_norm N)) (padded_original_direction_probability hk z)
    (padded_paired_direction_probability hk he hek hN z) hp.1 hp.2 hsolve'.1 hp'.2 hsolve.2 hsolve'.2 heps
  rw [← program.totalOutput_flagged out UA U node psi hpos, ← program.totalOutput_flagged out UA V node psi hpos'] at hsep
  have hhybrid := program.one_sided_vector_hybrid out UA U V node psi hpsi q hq
  have hd := padded_preparation_distance hk he hek hN
  have hbound := hsep.trans (hhybrid.trans (mul_le_mul_of_nonneg_left hd (by positivity)))
  have hbound' : (1 / 10 : ℝ) ≤ (15 * (q : ℝ) * estimate) / (2 * kappa) := by convert hbound using 1; ring
  have h := (le_div_iff₀ (show 0 < 2 * kappa by linarith)).mp hbound'
  apply (div_le_iff₀ (show 0 < 75 * estimate by positivity)).mpr
  nlinarith

/-- Correctness on every promised Hermitian input is specialized to the actual
original and paired inputs through literal PhysicalExactQLSPromise proofs. -/
theorem QuantumProgram.physical_same_instance_lower_bound
    {N m : ℕ} [NeZero N] [NeZero m] {kappa estimate eps : ℝ}
    (hk : 8 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (heps : 0 < eps) (hsmall : eps ≤ Real.exp (-16))
    (hm : m = logarithmicParityLength kappa eps)
    (hN : N = 2 * historyPadding kappa + 2 * m) {Node : ℕ → Type r} {w : ℕ}
    (program : QuantumProgram (OptimalQLS.SignalIndex 1 × Fin (paddedDimension N))
      (Fin (paddedDimension N)) (paddedDimension N) Node)
    (out : Fin (paddedDimension N)) (node : Node w) (psi : Fin w → ℂ) (hpsi : ‖WithLp.toLp 2 psi‖ = 1)
    (hcorrect : program.CorrectHermitianPhysicalQLS (d := hardOutputDimension N) (canonicalLowerParameters kappa estimate eps) out node psi) :
    ∃ z : BitString m,
      PhysicalExactQLSPromise (canonicalLowerParameters kappa estimate eps)
        (canonicalHardMatrix N kappa z) (canonicalHardSource N m kappa estimate)
        (paddedEncoding (N := N) (show 4 ≤ kappa by linarith) z)
        (paddedPreparation (show 4 ≤ kappa by linarith) he hek hN) ∧
      EntrywiseReal (canonicalHardMatrix N kappa z) ∧ (canonicalHardMatrix N kappa z).IsHermitian ∧
      ‖canonicalHardMatrix N kappa z‖ = 1 ∧ ‖Ring.inverse (canonicalHardMatrix N kappa z)‖ = kappa ∧
      (hardOutputDimension N : ℝ) ≤ 9 * kappa * Real.log (1 / eps) ∧
      (∀ qA : ℕ, program.PointwiseMatrixBound out
        (paddedEncoding (N := N) (show 4 ≤ kappa by linarith) z)
        (paddedPreparation (show 4 ≤ kappa by linarith) he hek hN) node psi qA →
        kappa * Real.log (1 / eps) / 192 ≤ (qA : ℝ)) ∧
      (∀ qB : ℕ, program.PointwiseVectorBound out
        (paddedEncoding (N := N) (show 4 ≤ kappa by linarith) z)
        (paddedPreparation (show 4 ≤ kappa by linarith) he hek hN) node psi qB →
        kappa / (75 * estimate) ≤ (qB : ℝ)) := by
  have hk4 : 4 ≤ kappa := by linarith
  have hepsUpper : eps < 1 / 2 := lt_of_le_of_lt (logarithmic_accuracy_vector_small hsmall) (by norm_num)
  have hsolve (z : BitString m) : program.Solves out (paddedEncoding (N := N) hk4 z)
      (paddedPreparation hk4 he hek hN) node psi (paddedSolution N kappa estimate z) eps := by
    have h := hcorrect (canonicalHardMatrix N kappa z) (canonicalHardSource N m kappa estimate)
      (paddedEncoding hk4 z) (paddedPreparation hk4 he hek hN) (canonicalHardMatrix_hermitian kappa z)
      (paddedHard_ExactQLSPromise hk4 he hek heps hepsUpper hN z)
    rw [paddedSolution_physicalSolution hk4 he hek hN z] at h
    exact h
  have hsolve' (z : BitString m) : program.Solves out (paddedEncoding (N := N) hk4 z)
      (paddedPerturbedPreparation hk4 he hek hN) node psi (paddedPairedSolution N kappa estimate z) eps := by
    have h := hcorrect (canonicalHardMatrix N kappa z) (canonicalPerturbedSource N m kappa estimate)
      (paddedEncoding hk4 z) (paddedPerturbedPreparation hk4 he hek hN) (canonicalHardMatrix_hermitian kappa z)
      (paddedPerturbed_ExactQLSPromise hk4 he hek heps hepsUpper hN z)
    rw [paddedPairedSolution_physicalSolution hk4 he z] at h
    exact h
  have hgap : 2 * eps < (5 / 2304 : ℝ) * historyLambda kappa ^ (2 * m) := by
    have h := logarithmic_signal_strict hk heps hsmall
    rw [← hm] at h
    linarith
  obtain ⟨z, fuel, k, hborn, hqueries⟩ := program.matrix_hard_run_of_solver out
    (paddedPolynomial hk4 hN) (paddedPolynomial_degree hk4 hN)
    (fun z => paddedEncoding (N := N) hk4 z) (paddedPreparation hk4 he hek hN)
    (paddedPolynomial_eval hk4 hN) node psi hpsi (paddedSolution N kappa estimate)
    (paddedWeight hk4 hN) (paddedWeight_bound hk4 hN) hgap hsolve (fun z => padded_signal hk4 he hek hN z)
  refine ⟨z, paddedHard_ExactQLSPromise hk4 he hek heps hepsUpper hN z,
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
    exact program.physical_pointwise_vector_lower_bound hk4 he hek hN z out node psi hpsi
      (hsolve z) (hsolve' z) (logarithmic_accuracy_vector_small hsmall) qB hqB

end OptimalQLS.LowerBounds
