import OptimalQLS.PhysicalPadding.Input

/-! Literal physical promises for Theorem 7.2. The original norm bound is
stated separately from approximation, exactly as in the source theorem. -/
noncomputable section
namespace OptimalQLS.PhysicalRobustness
open PhysicalPadding Matrix
open scoped Matrix.Norms.L2Operator
variable {d : ℕ} [NeZero d]

structure PhysicalApproximateQLSPromise (p : QLSParameters) (δ : ℝ)
    (A : Matrix (Fin d) (Fin d) ℂ) (b : DataSpace d)
    (UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × PhysicalData d) ℂ)
    (Ub : Matrix.unitaryGroup (PhysicalData d) ℂ) : Prop where
  invertible : IsUnit A
  unitVector : ‖b‖=1
  normBound : ‖A‖≤p.alpha
  approximateEncoding : IsBlockEncoding (0 : SignalIndex p.signalQubits) p.alpha δ UA (physicalMatrix A)
  statePreparation : ∀ i : PhysicalData d, Ub i 0=activeIsometry d b i
  kappaLower : 2≤p.kappa
  inverseBound : p.alpha*‖Ring.inverse A‖≤p.kappa
  epsilonPositive : 0<p.epsilon
  epsilonUpper : p.epsilon<1/2
  estimateLower : solutionScale p.alpha A b/2≤p.normEstimate
  estimateUpper : p.normEstimate≤2*solutionScale p.alpha A b
  smallError : p.kappa*δ/p.alpha≤1/4

/-- The complete supplied signal-zero compression, including cross-support
entries; the whole input oracle is never replaced by a chosen completion. -/
def actualCompressedMatrix (p : QLSParameters)
    (UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × PhysicalData d) ℂ) :
    Matrix (PhysicalData d) (PhysicalData d) ℂ :=
  p.alpha • signalBlock (0 : SignalIndex p.signalQubits) UA

variable {p : QLSParameters} {δ : ℝ} {A : Matrix (Fin d) (Fin d) ℂ} {b : DataSpace d}
  {UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × PhysicalData d) ℂ}
  {Ub : Matrix.unitaryGroup (PhysicalData d) ℂ}

theorem PhysicalApproximateQLSPromise.actual_exact (h : PhysicalApproximateQLSPromise p δ A b UA Ub) :
    IsBlockEncoding (0 : SignalIndex p.signalQubits) p.alpha 0 UA (actualCompressedMatrix p UA) :=
  ⟨h.approximateEncoding.1,by norm_num,by simp [actualCompressedMatrix]⟩

theorem PhysicalApproximateQLSPromise.actual_norm (h : PhysicalApproximateQLSPromise p δ A b UA Ub) :
    ‖actualCompressedMatrix p UA‖≤p.alpha := norm_le_of_exact_block h.actual_exact

theorem PhysicalApproximateQLSPromise.actual_error (h : PhysicalApproximateQLSPromise p δ A b UA Ub) :
    ‖actualCompressedMatrix p UA-physicalMatrix A‖≤δ := by
  rw [norm_sub_rev]
  exact h.approximateEncoding.2.2

/-- The source's independent original norm premise yields s≥1. Approximate
encoding alone is deliberately not used to establish this lower bound. -/
theorem PhysicalApproximateQLSPromise.scale_bounds (h : PhysicalApproximateQLSPromise p δ A b UA Ub) :
    1≤solutionScale p.alpha A b ∧ solutionScale p.alpha A b≤p.kappa := by
  let φ := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)
  have hu : IsUnit (φ A) := h.invertible.map φ.toMonoidHom
  have he : φ A (φ (Ring.inverse A) b)=b := by
    rw [Perturbation.toEuclideanCLM_inverse A h.invertible]
    exact Perturbation.apply_inverse _ hu b
  constructor
  · calc
      1 = ‖φ A (φ (Ring.inverse A) b)‖ := by rw [he,h.unitVector]
      _ ≤ ‖φ A‖*‖φ (Ring.inverse A) b‖ := (φ A).le_opNorm _
      _ ≤ p.alpha*‖φ (Ring.inverse A) b‖ :=
        mul_le_mul_of_nonneg_right h.normBound (norm_nonneg _)
  · have hn := (φ (Ring.inverse A)).le_opNorm b
    rw [h.unitVector,mul_one] at hn
    exact (mul_le_mul_of_nonneg_left hn h.approximateEncoding.1.le).trans h.inverseBound

end OptimalQLS.PhysicalRobustness
