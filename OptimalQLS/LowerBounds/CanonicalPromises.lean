import OptimalQLS.LowerBounds.CanonicalCoordinates

/-! Original and paired hard inputs satisfy the literal conventional Problem2.2 promise. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix

def canonicalLowerParameters (kappa estimate eps : ℝ) : OptimalQLS.QLSParameters where
  alpha := 1
  signalQubits := 1
  kappa := kappa
  normEstimate := estimate
  epsilon := eps

theorem solutionScale_one_reindex {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (M : Matrix D D ℂ) (b : D → ℂ) (e : E ≃ D) :
    OptimalQLS.solutionScale 1 (M.submatrix e e) (WithLp.toLp 2 (b ∘ e)) = ‖WithLp.toLp 2 (M⁻¹ *ᵥ b)‖ := by
  rw [OptimalQLS.solutionScale, one_mul, ← Matrix.nonsing_inv_eq_ringInverse]
  change ‖WithLp.toLp 2 ((M.submatrix e e)⁻¹ *ᵥ (b ∘ e))‖ = _
  rw [inverse_mulVec_reindex, euclidean_norm_comp_equiv]

theorem canonicalHardSource_norm {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) : ‖canonicalHardSource N m kappa estimate‖ = 1 := by
  rw [canonicalHardSource, euclidean_norm_comp_equiv]
  exact hardFamilySource_norm hk he hek hN

theorem canonicalPerturbedSource_norm {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) : ‖canonicalPerturbedSource N m kappa estimate‖ = 1 := by
  rw [canonicalPerturbedSource, euclidean_norm_comp_equiv]
  exact hardFamilyPerturbedSource_norm hk he hek hN

theorem canonicalHard_solutionScale {N m : ℕ} [NeZero N] (kappa estimate : ℝ) (z : BitString m) :
    OptimalQLS.solutionScale 1 (canonicalHardMatrix N kappa z) (canonicalHardSource N m kappa estimate) =
      ‖WithLp.toLp 2 ((hardFamilyMatrix N kappa z)⁻¹ *ᵥ hardFamilySource N m kappa estimate)‖ :=
  solutionScale_one_reindex _ _ _

theorem canonicalPerturbed_solutionScale {N m : ℕ} [NeZero N] (kappa estimate : ℝ) (z : BitString m) :
    OptimalQLS.solutionScale 1 (canonicalHardMatrix N kappa z) (canonicalPerturbedSource N m kappa estimate) =
      ‖WithLp.toLp 2 ((hardFamilyMatrix N kappa z)⁻¹ *ᵥ hardFamilyPerturbedSource N m kappa estimate)‖ :=
  solutionScale_one_reindex _ _ _

/-- Every original member obeys exactly the parent's Fin/zero-signal/zero-input
Problem2.2 definition, with alpha1 and one signal qubit. -/
theorem canonicalHard_ExactQLSPromise {N m : ℕ} [NeZero N] {kappa estimate eps : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (heps : 0 < eps) (hepsUpper : eps < 1 / 2)
    (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    OptimalQLS.ExactQLSPromise (canonicalLowerParameters kappa estimate eps)
      (canonicalHardMatrix N kappa z) (canonicalHardSource N m kappa estimate)
      (canonicalHardEncoding (N := N) hk z) (canonicalHardPreparation hk he hek hN) := by
  refine ⟨⟨canonicalHardMatrix_isUnit hk z, canonicalHardSource_norm hk he hek hN,
    canonicalHardEncoding_exact hk z, canonicalHardPreparation_prepares hk he hek hN,
    (by change 2 ≤ kappa; linarith), ?_, heps, hepsUpper⟩, ?_, ?_⟩
  · change 1 * ‖Ring.inverse (canonicalHardMatrix N kappa z)‖ ≤ kappa
    rw [canonicalHardMatrix_inverse_norm hk z, one_mul]
  · change OptimalQLS.solutionScale 1 _ _ / 2 ≤ estimate
    rw [canonicalHard_solutionScale]
    exact (hardFamily_solution_factor_two hk he hek hN z).1
  · change estimate ≤ 2 * OptimalQLS.solutionScale 1 _ _
    rw [canonicalHard_solutionScale]
    exact (hardFamily_solution_factor_two hk he hek hN z).2

/-- The same kappa, supplied norm estimate, precision, matrix and exact matrix
oracle remain promised after the explicit nearby source/preparation change. -/
theorem canonicalPerturbed_ExactQLSPromise {N m : ℕ} [NeZero N] {kappa estimate eps : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (heps : 0 < eps) (hepsUpper : eps < 1 / 2)
    (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    OptimalQLS.ExactQLSPromise (canonicalLowerParameters kappa estimate eps)
      (canonicalHardMatrix N kappa z) (canonicalPerturbedSource N m kappa estimate)
      (canonicalHardEncoding (N := N) hk z) (canonicalPerturbedPreparation hk he hek hN) := by
  refine ⟨⟨canonicalHardMatrix_isUnit hk z, canonicalPerturbedSource_norm hk he hek hN,
    canonicalHardEncoding_exact hk z, canonicalPerturbedPreparation_prepares hk he hek hN,
    (by change 2 ≤ kappa; linarith), ?_, heps, hepsUpper⟩, ?_, ?_⟩
  · change 1 * ‖Ring.inverse (canonicalHardMatrix N kappa z)‖ ≤ kappa
    rw [canonicalHardMatrix_inverse_norm hk z, one_mul]
  · change OptimalQLS.solutionScale 1 _ _ / 2 ≤ estimate
    rw [canonicalPerturbed_solutionScale]
    exact (hardFamilyPerturbed_solution_factor_two hk he hek hN z).1
  · change estimate ≤ 2 * OptimalQLS.solutionScale 1 _ _
    rw [canonicalPerturbed_solutionScale]
    exact (hardFamilyPerturbed_solution_factor_two hk he hek hN z).2

def canonicalSolution (N : ℕ) [NeZero N] {m : ℕ} (kappa estimate : ℝ) (z : BitString m) :
    Fin (hardOutputDimension N) → ℂ := normalizedHardFamilySolution N kappa estimate z ∘ canonicalDataCoordinates N

def canonicalPairedSolution (N : ℕ) [NeZero N] {m : ℕ} (kappa estimate : ℝ) (z : BitString m) :
    Fin (hardOutputDimension N) → ℂ := hardFamilyPairedSolution N kappa estimate z ∘ canonicalDataCoordinates N

theorem canonicalSolution_normalizedSolution {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    OptimalQLS.normalizedSolution (canonicalHardMatrix N kappa z) (canonicalHardSource N m kappa estimate) =
      WithLp.toLp 2 (canonicalSolution N kappa estimate z) := by
  rw [OptimalQLS.normalizedSolution, NormedSpace.normalize, ← Matrix.nonsing_inv_eq_ringInverse]
  change ‖WithLp.toLp 2 ((canonicalHardMatrix N kappa z)⁻¹ *ᵥ
    (hardFamilySource N m kappa estimate ∘ canonicalDataCoordinates N))‖⁻¹ •
      WithLp.toLp 2 ((canonicalHardMatrix N kappa z)⁻¹ *ᵥ
        (hardFamilySource N m kappa estimate ∘ canonicalDataCoordinates N)) = _
  rw [canonicalHardMatrix, inverse_mulVec_reindex, euclidean_norm_comp_equiv, hardFamily_solution_norm hk he hek hN z]
  rfl

theorem canonicalPairedSolution_normalizedSolution {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (z : BitString m) :
    OptimalQLS.normalizedSolution (canonicalHardMatrix N kappa z) (canonicalPerturbedSource N m kappa estimate) =
      WithLp.toLp 2 (canonicalPairedSolution N kappa estimate z) := by
  rw [OptimalQLS.normalizedSolution, NormedSpace.normalize, ← Matrix.nonsing_inv_eq_ringInverse]
  change ‖WithLp.toLp 2 ((canonicalHardMatrix N kappa z)⁻¹ *ᵥ
    (hardFamilyPerturbedSource N m kappa estimate ∘ canonicalDataCoordinates N))‖⁻¹ •
      WithLp.toLp 2 ((canonicalHardMatrix N kappa z)⁻¹ *ᵥ
        (hardFamilyPerturbedSource N m kappa estimate ∘ canonicalDataCoordinates N)) = _
  rw [canonicalHardMatrix, inverse_mulVec_reindex, euclidean_norm_comp_equiv]
  unfold canonicalPairedSolution
  rw [hardFamilyPairedSolution_eq_normalized_inverse hk he z]
  rfl

end OptimalQLS.LowerBounds
