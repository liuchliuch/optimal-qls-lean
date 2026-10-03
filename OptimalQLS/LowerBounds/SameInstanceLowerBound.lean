import OptimalQLS.LowerBounds.QuantumHardLower
import OptimalQLS.LowerBounds.LogarithmicChoice

/-!
# Simultaneous lower bounds on one member of one concrete family

The program is the actual unbounded, finitely branching instruction
coalgebra, with changing finite quantum registers and nontermination counted
as failure. The two resource bounds use this same program, same original
oracle pair, and literal positive-Born finite execution prefixes.

Correctness is required only on the constructed original and paired inputs;
a solver correct on all promised QLS inputs satisfies this requirement.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
universe r

theorem logarithmic_accuracy_vector_small {eps : ℝ} (hsmall : eps ≤ Real.exp (-16)) : eps ≤ 1 / 64 := by
  have h8 : (9 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  have h16 : (64 : ℝ) ≤ Real.exp 16 := by
    rw [show (16 : ℝ) = 8 + 8 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos (8 : ℝ)]
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 64) h16
  apply hsmall.trans
  simpa only [one_div, Real.exp_neg] using h

/-- Explicit same-instance query lower bounds with constants1/192 and1/75.
The selected z is shared by the matrix and vector conclusions. -/
theorem QuantumProgram.same_instance_query_lower_bounds
    {N m : ℕ} [NeZero N] [NeZero m] {kappa estimate eps : ℝ}
    (hk : 8 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (heps : 0 < eps) (hsmall : eps ≤ Real.exp (-16))
    (hm : m = logarithmicParityLength kappa eps)
    (hN : N = 2 * historyPadding kappa + 2 * m) {Node : ℕ → Type r} {w : ℕ}
    (program : QuantumProgram (Bool × HardFamilyIndex N) (HardFamilyIndex N) (hardOutputDimension N) Node)
    (out : Fin (hardOutputDimension N)) (node : Node w) (psi : Fin w → ℂ) (hpsi : ‖WithLp.toLp 2 psi‖ = 1)
    (hsolve : ∀ z : BitString m, program.Solves out
      (hardFamilyEncoding (N := N) (show 4 ≤ kappa by linarith) z)
      (hardFamilyPreparation (show 4 ≤ kappa by linarith) he hek hN)
      node psi (hardOutputSolution N kappa estimate z) eps)
    (hsolve' : ∀ z : BitString m, program.Solves out
      (hardFamilyEncoding (N := N) (show 4 ≤ kappa by linarith) z)
      (hardFamilyPerturbedPreparation (show 4 ≤ kappa by linarith) he hek hN)
      node psi (hardOutputPairedSolution N kappa estimate z) eps) :
    (hardOutputDimension N : ℝ) ≤ 9 * kappa * Real.log (1 / eps) ∧
    ∃ z : BitString m,
      (∀ qA : ℕ, program.PointwiseMatrixBound out
        (hardFamilyEncoding (N := N) (show 4 ≤ kappa by linarith) z)
        (hardFamilyPreparation (show 4 ≤ kappa by linarith) he hek hN) node psi qA →
        kappa * Real.log (1 / eps) / 192 ≤ (qA : ℝ)) ∧
      (∀ qB : ℕ, program.PointwiseVectorBound out
        (hardFamilyEncoding (N := N) (show 4 ≤ kappa by linarith) z)
        (hardFamilyPreparation (show 4 ≤ kappa by linarith) he hek hN) node psi qB →
        kappa / (75 * estimate) ≤ (qB : ℝ)) := by
  have hk4 : 4 ≤ kappa := by linarith
  have hsig : 2 * eps < (5 / 2304 : ℝ) * historyLambda kappa ^ (2 * m) := by
    have h := logarithmic_signal_strict hk heps hsmall
    rw [← hm] at h
    linarith
  have hmlower : kappa * Real.log (1 / eps) / 96 ≤ (m : ℝ) := by
    rw [hm]
    exact (logarithmicParityLength_bounds hk heps hsmall).2.1
  have hNlog : N = logarithmicHistorySize kappa eps := by simp only [logarithmicHistorySize, ← hm, hN]
  refine ⟨?_, ?_⟩
  · rw [hardOutputDimension, hNlog]
    exact logarithmicHardFamily_dimension_upper hk heps hsmall
  · obtain ⟨z, fuel, k, hborn, hqueries⟩ := program.hard_family_matrix_hard_run hk4 he hek hN out node psi hpsi hsig hsolve
    refine ⟨z, ?_, ?_⟩
    · intro qA hqA
      have hq := hqA fuel k hborn
      have hnat : m ≤ 2 * qA := hqueries.trans (Nat.mul_le_mul_left 2 hq)
      have hreal : (m : ℝ) ≤ 2 * (qA : ℝ) := by exact_mod_cast hnat
      linarith
    · intro qB hqB
      exact program.hard_family_pointwise_vector_lower_bound hk4 he hek hN z out node psi hpsi
        (hsolve z) (hsolve' z) (logarithmic_accuracy_vector_small hsmall) qB hqB

end OptimalQLS.LowerBounds
