import OptimalQLS.BlockEncoding

/-!
# Exact input promises of Problem 2.2

Classical parameters are separate from oracle matrices. In particular, the
solution-norm estimate is an actual supplied parameter; it is not silently
computed from the hidden matrix or replaced by the exact norm.
-/
noncomputable section
namespace OptimalQLS
open scoped Matrix.Norms.L2Operator

structure QLSParameters where
  alpha : ℝ
  signalQubits : ℕ
  kappa : ℝ
  normEstimate : ℝ
  epsilon : ℝ

abbrev SignalIndex (a : ℕ) := Fin (2 ^ a)
abbrev DataSpace (d : ℕ) := EuclideanSpace ℂ (Fin d)

def normalizedSolution {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (b : DataSpace d) : DataSpace d :=
  NormedSpace.normalize (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (Ring.inverse A) b)

variable {d : ℕ} [NeZero d]

/-- The common input promises, with the literal zero-signal block and the
entire state-preparation unitary, not merely access to copies of b. -/
structure BaseQLSPromise (p : QLSParameters) (A : Matrix (Fin d) (Fin d) ℂ)
    (b : DataSpace d)
    (UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × Fin d) ℂ)
    (Ub : Matrix.unitaryGroup (Fin d) ℂ) : Prop where
  invertible : IsUnit A
  unitVector : ‖b‖ = 1
  exactEncoding : IsBlockEncoding (0 : SignalIndex p.signalQubits) p.alpha 0 UA A
  statePreparation : ∀ i : Fin d, Ub i 0 = b i
  kappaLower : 2 ≤ p.kappa
  inverseBound : p.alpha * ‖Ring.inverse A‖ ≤ p.kappa
  epsilonPositive : 0 < p.epsilon
  epsilonUpper : p.epsilon < 1 / 2

/-- The stated factor-two estimate in Problem 2.2 and Theorem 5.7. -/
structure ExactQLSPromise (p : QLSParameters) (A : Matrix (Fin d) (Fin d) ℂ)
    (b : DataSpace d)
    (UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × Fin d) ℂ)
    (Ub : Matrix.unitaryGroup (Fin d) ℂ)
    : Prop extends BaseQLSPromise p A b UA Ub where
  estimateLower : solutionScale p.alpha A b / 2 ≤ p.normEstimate
  estimateUpper : p.normEstimate ≤ 2 * solutionScale p.alpha A b

/-- The explicitly relaxed promise used internally and in robustness. -/
structure RelaxedQLSPromise (p : QLSParameters) (A : Matrix (Fin d) (Fin d) ℂ)
    (b : DataSpace d)
    (UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × Fin d) ℂ)
    (Ub : Matrix.unitaryGroup (Fin d) ℂ)
    : Prop extends BaseQLSPromise p A b UA Ub where
  estimateLower : 3 * solutionScale p.alpha A b / 8 ≤ p.normEstimate
  estimateUpper : p.normEstimate ≤ 5 * solutionScale p.alpha A b / 2

theorem BaseQLSPromise.scale_bounds {p : QLSParameters}
    {A : Matrix (Fin d) (Fin d) ℂ} {b : DataSpace d}
    {UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × Fin d) ℂ}
    {Ub : Matrix.unitaryGroup (Fin d) ℂ} (h : BaseQLSPromise p A b UA Ub) :
    1 ≤ solutionScale p.alpha A b ∧ solutionScale p.alpha A b ≤ p.kappa :=
  solutionScale_bounds h.exactEncoding h.invertible h.inverseBound b h.unitVector

theorem ExactQLSPromise.toRelaxed {p : QLSParameters}
    {A : Matrix (Fin d) (Fin d) ℂ} {b : DataSpace d}
    {UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × Fin d) ℂ}
    {Ub : Matrix.unitaryGroup (Fin d) ℂ} (h : ExactQLSPromise p A b UA Ub) :
    RelaxedQLSPromise p A b UA Ub := by
  have hs := h.toBaseQLSPromise.scale_bounds.1
  exact { toBaseQLSPromise := h.toBaseQLSPromise
          estimateLower := by linarith [h.estimateLower]
          estimateUpper := by linarith [h.estimateUpper] }

theorem BaseQLSPromise.solution_unit {p : QLSParameters}
    {A : Matrix (Fin d) (Fin d) ℂ} {b : DataSpace d}
    {UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × Fin d) ℂ}
    {Ub : Matrix.unitaryGroup (Fin d) ℂ} (h : BaseQLSPromise p A b UA Ub) :
    ‖normalizedSolution A b‖ = 1 := by
  apply NormedSpace.norm_normalize
  have hb : b ≠ 0 := by intro hb; simpa [hb] using h.unitVector
  rw [Perturbation.toEuclideanCLM_inverse A h.invertible]
  exact Perturbation.inverse_apply_ne_zero _
    (h.invertible.map (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).toMonoidHom) hb

end OptimalQLS
