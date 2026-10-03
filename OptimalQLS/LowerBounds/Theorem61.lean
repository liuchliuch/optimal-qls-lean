import OptimalQLS.LowerBounds.CanonicalLowerBounds

/-!
# Theorem6.1: a single conventional promised input is hard for both oracles

Explicit absolute constants are kappa0=8 and epsilon0=exp(-16). The selected
matrix has norm1, inverse normkappa, real Hermitian entries, one exact signal
qubit, and dimension at most9*kappa*log(1/epsilon). Both query bounds are on the
same original input of one actual unbounded quantum instruction program.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
universe r

/-- The operational same-instance conclusion at a fixed data dimension. Every
resource bound is defined by positive Born runs of actual finite prefixes. -/
def SameInstanceQLSLowerProperty (kappa estimate eps : ℝ) (d : ℕ) [NeZero d] : Prop :=
  ∀ (Node : ℕ → Type r) (w : ℕ)
    (program : QuantumProgram (OptimalQLS.SignalIndex 1 × Fin d) (Fin d) d Node)
    (out : Fin d) (node : Node w) (psi : Fin w → ℂ), ‖WithLp.toLp 2 psi‖ = 1 →
    program.CorrectHermitianQLS (canonicalLowerParameters kappa estimate eps) out node psi →
    ∃ (M : Matrix (Fin d) (Fin d) ℂ) (b : OptimalQLS.DataSpace d)
      (UA : Matrix.unitaryGroup (OptimalQLS.SignalIndex 1 × Fin d) ℂ)
      (Ub : Matrix.unitaryGroup (Fin d) ℂ),
      OptimalQLS.ExactQLSPromise (canonicalLowerParameters kappa estimate eps) M b UA Ub ∧
      EntrywiseReal M ∧ M.IsHermitian ∧ ‖M‖ = 1 ∧ ‖Ring.inverse M‖ = kappa ∧
      (∀ qA : ℕ, program.PointwiseMatrixBound out UA Ub node psi qA →
        kappa * Real.log (1 / eps) / 192 ≤ (qA : ℝ)) ∧
      (∀ qB : ℕ, program.PointwiseVectorBound out UA Ub node psi qB →
        kappa / (75 * estimate) ≤ (qB : ℝ))

/-- The manuscript's simultaneous lower-bound theorem in conventional
Problem2.2 coordinates, with fully explicit constants and one signal qubit. -/
theorem theorem61 {kappa estimate eps : ℝ} (hk : 8 ≤ kappa)
    (he : 1 ≤ estimate) (hek : estimate ≤ kappa) (heps : 0 < eps) (hsmall : eps ≤ Real.exp (-16)) :
    ∃ (d : ℕ) (hd : 0 < d), (d : ℝ) ≤ 9 * kappa * Real.log (1 / eps) ∧
      @SameInstanceQLSLowerProperty.{r} kappa estimate eps d ⟨Nat.ne_of_gt hd⟩ := by
  let m := logarithmicParityLength kappa eps
  let N := logarithmicHistorySize kappa eps
  have hmpos : 0 < m := by have h := (logarithmicParityLength_bounds hk heps hsmall).1; omega
  have hNpos : 0 < N := logarithmicHistorySize_pos hk heps hsmall
  letI : NeZero m := ⟨Nat.ne_of_gt hmpos⟩
  letI : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
  have hN : N = 2 * historyPadding kappa + 2 * m := rfl
  have hk4 : 4 ≤ kappa := by linarith
  refine ⟨hardOutputDimension N, hardOutputDimension_pos N, ?_, ?_⟩
  · exact logarithmicHardFamily_dimension_upper hk heps hsmall
  · intro Node w program out node psi hpsi hcorrect
    obtain ⟨z, hpromise, hreal, hhermitian, hnorm, hinverse, hdimension, hmatrix, hvector⟩ :=
      program.canonical_same_instance_lower_bound (N := N) (m := m) hk he hek heps hsmall rfl hN
        out node psi hpsi hcorrect
    exact ⟨canonicalHardMatrix N kappa z, canonicalHardSource N m kappa estimate,
      canonicalHardEncoding hk4 z, canonicalHardPreparation hk4 he hek hN,
      hpromise, hreal, hhermitian, hnorm, hinverse, hmatrix, hvector⟩

end OptimalQLS.LowerBounds
