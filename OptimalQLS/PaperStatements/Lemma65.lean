import OptimalQLS.LowerBounds.Physical.LowerBounds

/-! Lemma 6.5 specialized directly from universal physical correctness.
The bound concerns each original family member, including all its reachable
positive-Born finite prefixes; no cap on its rotated companion is assumed. -/
noncomputable section
open scoped Matrix.Norms.L2Operator
namespace OptimalQLS.PaperStatements
open Matrix LowerBounds LowerBounds.Physical PhysicalPadding
universe r

theorem lemma65 {N m : ℕ} [NeZero N] {κ ŝ ε : ℝ}
    (hκ : 4 ≤ κ) (hŝ : 1 ≤ ŝ) (hŝκ : ŝ ≤ κ)
    (hε : 0 < ε) (hεv : ε ≤ 1/64)
    (hN : N = 2 * historyPadding κ + 2 * m)
    {Node : ℕ → Type r} {w : ℕ}
    (program : QuantumProgram (SignalIndex 1 × Fin (paddedDimension N))
      (Fin (paddedDimension N)) (paddedDimension N) Node)
    (out : Fin (paddedDimension N)) (node : Node w) (ψ : Fin w → ℂ)
    (hψ : ‖WithLp.toLp 2 ψ‖ = 1)
    (hcorrect : program.CorrectHermitianPhysicalQLS (d := hardOutputDimension N)
      (canonicalLowerParameters κ ŝ ε) out node ψ) :
    ∀ z : BitString m,
      PhysicalExactQLSPromise (canonicalLowerParameters κ ŝ ε)
        (canonicalHardMatrix N κ z) (canonicalHardSource N m κ ŝ)
        (paddedEncoding hκ z) (paddedPreparation hκ hŝ hŝκ hN) ∧
      ∀ q : ℕ, program.PointwiseVectorBound out (paddedEncoding hκ z)
        (paddedPreparation hκ hŝ hŝκ hN) node ψ q → κ/(75*ŝ) ≤ (q : ℝ) := by
  have hεhalf : ε < 1/2 := by linarith
  intro z
  have hp := paddedHard_ExactQLSPromise hκ hŝ hŝκ hε hεhalf hN z
  have hp' := paddedPerturbed_ExactQLSPromise hκ hŝ hŝκ hε hεhalf hN z
  have hs := hcorrect (canonicalHardMatrix N κ z) (canonicalHardSource N m κ ŝ)
    (paddedEncoding hκ z) (paddedPreparation hκ hŝ hŝκ hN)
    (canonicalHardMatrix_hermitian κ z) hp
  have hs' := hcorrect (canonicalHardMatrix N κ z) (canonicalPerturbedSource N m κ ŝ)
    (paddedEncoding hκ z) (paddedPerturbedPreparation hκ hŝ hŝκ hN)
    (canonicalHardMatrix_hermitian κ z) hp'
  rw [paddedSolution_physicalSolution hκ hŝ hŝκ hN z] at hs
  rw [paddedPairedSolution_physicalSolution hκ hŝ z] at hs'
  refine ⟨hp, ?_⟩
  intro q hq
  exact program.physical_pointwise_vector_lower_bound hκ hŝ hŝκ hN z
    out node ψ hψ hs hs' hεv q hq

end OptimalQLS.PaperStatements
