import OptimalQLS.LowerBounds.Physical.LowerBounds

/-!
# Theorem 6.1 on actual complete physical qubit registers

The logical d-dimensional matrix is fully zero extended to precisely
ceil(log₂ d) data qubits. The universal algorithm can access every column of
its supplied physical unitaries. Both lower bounds hold on the same original
input and the same unrestricted unbounded instruction program.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds.Physical
open Matrix PhysicalPadding
universe r

/-- Universal physical-program same-instance lower bound. Correctness ranges
over all valid whole UA and Ub, not only the hard-family completions. -/
def SameInstancePhysicalQLSLowerProperty (kappa estimate eps : ℝ) (d : ℕ) [NeZero d] : Prop :=
  ∀ (Node : ℕ → Type r) (w : ℕ)
    (program : QuantumProgram (SignalIndex 1 × Fin (physicalDimension d))
      (Fin (physicalDimension d)) (physicalDimension d) Node)
    (out : Fin (physicalDimension d)) (node : Node w) (psi : Fin w → ℂ),
    ‖WithLp.toLp 2 psi‖ = 1 →
    program.CorrectHermitianPhysicalQLS (d := d)
      (canonicalLowerParameters kappa estimate eps) out node psi →
    ∃ (M : Matrix (Fin d) (Fin d) ℂ) (b : DataSpace d)
      (UA : Matrix.unitaryGroup (SignalIndex 1 × Fin (physicalDimension d)) ℂ)
      (Ub : Matrix.unitaryGroup (Fin (physicalDimension d)) ℂ),
      PhysicalExactQLSPromise (canonicalLowerParameters kappa estimate eps) M b UA Ub ∧
      EntrywiseReal M ∧ M.IsHermitian ∧ ‖M‖ = 1 ∧ ‖Ring.inverse M‖ = kappa ∧
      (∀ qA : ℕ, program.PointwiseMatrixBound out UA Ub node psi qA →
        kappa * Real.log (1 / eps) / 192 ≤ (qA : ℝ)) ∧
      (∀ qB : ℕ, program.PointwiseVectorBound out UA Ub node psi qB →
        kappa / (75 * estimate) ≤ (qB : ℝ))

/-- The physical oracle-domain form of the manuscript's simultaneous theorem.
Dimension and qubit count are chosen before the arbitrary algorithm, and the
matrix and vector bounds are both on one whole-oracle pair. -/
theorem theorem61 {kappa estimate eps : ℝ} (hk : 8 ≤ kappa)
    (he : 1 ≤ estimate) (hek : estimate ≤ kappa) (heps : 0 < eps)
    (hsmall : eps ≤ Real.exp (-16)) :
    ∃ (d n : ℕ) (hd : 0 < d),
      n = ⌈Real.log (d : ℝ) / Real.log 2⌉₊ ∧
      physicalDimension d = 2 ^ n ∧
      (d : ℝ) ≤ 9 * kappa * Real.log (1 / eps) ∧
      (physicalDimension d : ℝ) ≤ 18 * kappa * Real.log (1 / eps) ∧
      @SameInstancePhysicalQLSLowerProperty.{r} kappa estimate eps d ⟨Nat.ne_of_gt hd⟩ := by
  let m := logarithmicParityLength kappa eps
  let N := logarithmicHistorySize kappa eps
  have hmpos : 0 < m := by
    have h := (logarithmicParityLength_bounds hk heps hsmall).1
    omega
  have hNpos : 0 < N := logarithmicHistorySize_pos hk heps hsmall
  letI : NeZero m := ⟨Nat.ne_of_gt hmpos⟩
  letI : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
  have hN : N = 2 * historyPadding kappa + 2 * m := rfl
  have hk4 : 4 ≤ kappa := by linarith
  have hd := hardOutputDimension_pos N
  have hdim : (hardOutputDimension N : ℝ) ≤ 9 * kappa * Real.log (1 / eps) :=
    logarithmicHardFamily_dimension_upper hk heps hsmall
  refine ⟨hardOutputDimension N, dataQubits (hardOutputDimension N), hd,
    dataQubits_eq_ceil_log _, rfl, hdim, ?_, ?_⟩
  · have hp := physicalDimension_lt_twice hd
    have hp' : (physicalDimension (hardOutputDimension N) : ℝ) <
        2 * (hardOutputDimension N : ℝ) := by exact_mod_cast hp
    linarith
  · intro Node w program out node psi hpsi hcorrect
    obtain ⟨z, hpromise, hreal, hhermitian, hnorm, hinverse, hdimension, hmatrix, hvector⟩ :=
      program.physical_same_instance_lower_bound (N := N) (m := m) hk he hek heps hsmall rfl hN
        out node psi hpsi hcorrect
    exact ⟨canonicalHardMatrix N kappa z, canonicalHardSource N m kappa estimate,
      paddedEncoding hk4 z, paddedPreparation hk4 he hek hN,
      hpromise, hreal, hhermitian, hnorm, hinverse, hmatrix, hvector⟩

end OptimalQLS.LowerBounds.Physical
