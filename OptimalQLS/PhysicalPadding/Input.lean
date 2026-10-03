import OptimalQLS.PhysicalPadding.Operators

/-! Exact physical input promises in the source's full-zero-extension convention.
UA and Ub are arbitrary supplied whole unitaries; no chosen unitary completion
is substituted and no promise restricts off-signal blocks or other Ub columns. -/
noncomputable section
set_option linter.unusedSectionVars false
namespace OptimalQLS.PhysicalPadding
open Matrix
open scoped Matrix.Norms.L2Operator
variable {d : ℕ} [NeZero d]

abbrev PhysicalData (d : ℕ) := Fin (physicalDimension d)
abbrev PhysicalSource (d : ℕ) := EuclideanSpace ℂ (PhysicalData d)

/-- The normalized target lives in the physical register and uses only the
inverse of the original, promised invertible d-dimensional matrix. -/
def physicalSolution (A : Matrix (Fin d) (Fin d) ℂ) (b : DataSpace d) : PhysicalSource d :=
  activeIsometry d (normalizedSolution A b)

structure PhysicalBaseQLSPromise (p : QLSParameters) (A : Matrix (Fin d) (Fin d) ℂ)
    (b : DataSpace d)
    (UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × PhysicalData d) ℂ)
    (Ub : Matrix.unitaryGroup (PhysicalData d) ℂ) : Prop where
  invertible : IsUnit A
  unitVector : ‖b‖ = 1
  exactEncoding : IsBlockEncoding (0 : SignalIndex p.signalQubits) p.alpha 0 UA (physicalMatrix A)
  statePreparation : ∀ i : PhysicalData d, Ub i 0 = activeIsometry d b i
  kappaLower : 2 ≤ p.kappa
  inverseBound : p.alpha * ‖Ring.inverse A‖ ≤ p.kappa
  epsilonPositive : 0 < p.epsilon
  epsilonUpper : p.epsilon < 1 / 2

structure PhysicalExactQLSPromise (p : QLSParameters) (A : Matrix (Fin d) (Fin d) ℂ)
    (b : DataSpace d)
    (UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × PhysicalData d) ℂ)
    (Ub : Matrix.unitaryGroup (PhysicalData d) ℂ) : Prop
    extends PhysicalBaseQLSPromise p A b UA Ub where
  estimateLower : solutionScale p.alpha A b / 2 ≤ p.normEstimate
  estimateUpper : p.normEstimate ≤ 2 * solutionScale p.alpha A b

structure PhysicalRelaxedQLSPromise (p : QLSParameters) (A : Matrix (Fin d) (Fin d) ℂ)
    (b : DataSpace d)
    (UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × PhysicalData d) ℂ)
    (Ub : Matrix.unitaryGroup (PhysicalData d) ℂ) : Prop
    extends PhysicalBaseQLSPromise p A b UA Ub where
  estimateLower : 3 * solutionScale p.alpha A b / 8 ≤ p.normEstimate
  estimateUpper : p.normEstimate ≤ 5 * solutionScale p.alpha A b / 2

variable {p : QLSParameters} {A : Matrix (Fin d) (Fin d) ℂ} {b : DataSpace d}
  {UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × PhysicalData d) ℂ}
  {Ub : Matrix.unitaryGroup (PhysicalData d) ℂ}

theorem PhysicalBaseQLSPromise.logical_norm (h : PhysicalBaseQLSPromise p A b UA Ub) :
    ‖A‖ ≤ p.alpha := by
  rw [← zeroExtend_norm (activeIndex d) A]
  exact norm_le_of_exact_block h.exactEncoding

/-- All entries of the full signal compression are fixed, not just its active corner. -/
theorem PhysicalBaseQLSPromise.full_compression (h : PhysicalBaseQLSPromise p A b UA Ub) :
    physicalMatrix A = p.alpha • signalBlock (0 : SignalIndex p.signalQubits) UA :=
  exact_block_eq h.exactEncoding

theorem PhysicalBaseQLSPromise.source_unit (h : PhysicalBaseQLSPromise p A b UA Ub) :
    ‖activeIsometry d b‖ = 1 := by rw [(activeIsometry d).norm_map, h.unitVector]

theorem PhysicalBaseQLSPromise.source_preparation
    (h : PhysicalBaseQLSPromise p A b UA Ub) :
    Ub.val *ᵥ Pi.single (0 : PhysicalData d) 1 = WithLp.ofLp (activeIsometry d b) := by
  ext i
  simpa only [Matrix.mulVec_single_one] using h.statePreparation i

/-- The supplied solution-norm estimate has exactly the same scale after padding. -/
theorem physical_solutionScale (α : ℝ) (A : Matrix (Fin d) (Fin d) ℂ) (b : DataSpace d) :
    α * ‖Matrix.toEuclideanCLM (n := PhysicalData d) (𝕜 := ℂ)
      (activeInverse (activeIndex d) A) (activeIsometry d b)‖ = solutionScale α A b := by
  rw [activeInverse_apply, (activeIsometry d).norm_map]
  rfl

/-- Source errors are transported isometrically, including arbitrary complex phases. -/
theorem physical_source_error (b c : DataSpace d) :
    ‖activeIsometry d b - activeIsometry d c‖ = ‖b-c‖ :=
  isometry_norm_sub (activeIsometry d) b c

theorem PhysicalBaseQLSPromise.scale_bounds (h : PhysicalBaseQLSPromise p A b UA Ub) :
    1 ≤ solutionScale p.alpha A b ∧ solutionScale p.alpha A b ≤ p.kappa := by
  let φ := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)
  have hφA : IsUnit (φ A) := h.invertible.map φ.toMonoidHom
  have heq : φ A (φ (Ring.inverse A) b) = b := by
    rw [Perturbation.toEuclideanCLM_inverse A h.invertible]
    exact Perturbation.apply_inverse (φ A) hφA b
  constructor
  · calc
      1 = ‖φ A (φ (Ring.inverse A) b)‖ := by rw [heq, h.unitVector]
      _ ≤ ‖φ A‖ * ‖φ (Ring.inverse A) b‖ := (φ A).le_opNorm _
      _ ≤ p.alpha * ‖φ (Ring.inverse A) b‖ :=
        mul_le_mul_of_nonneg_right h.logical_norm (norm_nonneg _)
  · have hnorm := (φ (Ring.inverse A)).le_opNorm b
    rw [h.unitVector, mul_one] at hnorm
    exact (mul_le_mul_of_nonneg_left hnorm h.exactEncoding.1.le).trans h.inverseBound

theorem PhysicalExactQLSPromise.toRelaxed (h : PhysicalExactQLSPromise p A b UA Ub) :
    PhysicalRelaxedQLSPromise p A b UA Ub := by
  have hs := h.toPhysicalBaseQLSPromise.scale_bounds.1
  exact { toPhysicalBaseQLSPromise := h.toPhysicalBaseQLSPromise
          estimateLower := by linarith [h.estimateLower]
          estimateUpper := by linarith [h.estimateUpper] }

theorem physicalSolution_eq_normalize_activeInverse
    (A : Matrix (Fin d) (Fin d) ℂ) (b : DataSpace d) :
    physicalSolution A b = NormedSpace.normalize
      (Matrix.toEuclideanCLM (n := PhysicalData d) (𝕜 := ℂ)
        (activeInverse (activeIndex d) A) (activeIsometry d b)) := by
  rw [activeInverse_apply, isometry_normalize]
  rfl

theorem physicalSolution_eq_normalize_pseudoInverse
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (hunit : IsUnit A) (b : DataSpace d) :
    physicalSolution A b = NormedSpace.normalize
      (Matrix.toEuclideanCLM (n := PhysicalData d) (𝕜 := ℂ)
        (matrixPseudoInverse (physicalMatrix A) (zeroExtend_hermitian (activeIndex d) A hA))
        (activeIsometry d b)) := by
  rw [zeroExtend_pseudoInverse (activeIndex d) A hA, matrixPseudoInverse, StarAlgEquiv.apply_symm_apply,
    hermitianPseudoInverse_eq_inverse (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A)
      (matrixHermitian_symmetric A hA) (hunit.map (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).toMonoidHom),
    ← Perturbation.toEuclideanCLM_inverse A hunit, isometry_normalize]
  rfl

theorem PhysicalBaseQLSPromise.solution_unit (h : PhysicalBaseQLSPromise p A b UA Ub) :
    ‖physicalSolution A b‖ = 1 := by
  rw [physicalSolution, (activeIsometry d).norm_map]
  apply NormedSpace.norm_normalize
  have hb : b ≠ 0 := by intro hb; simpa [hb] using h.unitVector
  rw [Perturbation.toEuclideanCLM_inverse A h.invertible]
  exact Perturbation.inverse_apply_ne_zero _
    (h.invertible.map (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).toMonoidHom) hb

/-- The same norm-error criterion holds exactly before and after physical padding. -/
theorem physical_solution_error (A : Matrix (Fin d) (Fin d) ℂ) (b x : DataSpace d) :
    ‖activeIsometry d x - physicalSolution A b‖ = ‖x - normalizedSolution A b‖ :=
  isometry_norm_sub (activeIsometry d) x (normalizedSolution A b)

end OptimalQLS.PhysicalPadding
