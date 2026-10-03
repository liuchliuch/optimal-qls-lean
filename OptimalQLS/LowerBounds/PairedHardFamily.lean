import OptimalQLS.LowerBounds.PairedGeometry

/-! The perturbation of every original hard-family member is a valid QLS input. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix

variable {N m : ℕ} [NeZero N] {kappa estimate : ℝ}

def hardFamilyOrthogonalPair (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) :
    OrthogonalUnitPair (hardFamilySource N m kappa estimate) (dilatedLastDirection (D := HistoryBasis N)) :=
  orthogonalUnitPair_of_norm_inner _ _ (hardFamilySource_norm hk he hek hN) dilatedLastDirection_norm
    (hardFamily_source_orthogonal_direction kappa estimate)

def hardFamilyPerturbedSource (N m : ℕ) [NeZero N] (kappa estimate : ℝ) : HardFamilyIndex N → ℂ :=
  perturbedSource (hardFamilySource N m kappa estimate) dilatedLastDirection (vectorPerturbationSize kappa estimate)

def hardFamilyPerturbedPreparation (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) : Matrix.unitaryGroup (HardFamilyIndex N) ℂ :=
  perturbedPreparation (hardFamilySource N m kappa estimate) dilatedLastDirection
    (hardFamilyOrthogonalPair hk he hek hN) (vectorPerturbationSize kappa estimate)
    (hardFamilyPreparation hk he hek hN)

def hardFamilyPairedSolution (N : ℕ) [NeZero N] {m : ℕ} (kappa estimate : ℝ) (z : BitString m) :
    HardFamilyIndex N → ℂ := pairedNormalizedSolution
      ((hardFamilyMatrix N kappa z)⁻¹ *ᵥ hardFamilySource N m kappa estimate) dilatedLastDirection (5 * estimate / 4)

theorem hardFamily_direction_inverse (hk : 4 ≤ kappa) (z : BitString m) :
    (hardFamilyMatrix N kappa z)⁻¹ *ᵥ dilatedLastDirection = kappa • dilatedLastDirection :=
  inverse_eigen_direction _ _ (by linarith) (hardFamilyMatrix_isUnit hk z) (hardFamily_fixed_direction kappa z).2

theorem hardFamilyPerturbedSource_norm (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) : ‖WithLp.toLp 2 (hardFamilyPerturbedSource N m kappa estimate)‖ = 1 :=
  perturbedSource_norm _ _ _ (hardFamilySource_norm hk he hek hN) dilatedLastDirection_norm
    (hardFamily_source_orthogonal_direction kappa estimate)

theorem hardFamilyPerturbedPreparation_prepares (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) :
    ∀ i, hardFamilyPerturbedPreparation hk he hek hN i (.inl (.inl ())) = hardFamilyPerturbedSource N m kappa estimate i :=
  perturbedPreparation_prepares _ _ _ _ _ _ (hardFamilyPreparation_prepares hk he hek hN)

theorem hardFamilyPerturbedPreparation_distance (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) :
    ‖(hardFamilyPerturbedPreparation hk he hek hN : Matrix (HardFamilyIndex N) (HardFamilyIndex N) ℂ) -
      (hardFamilyPreparation hk he hek hN : Matrix (HardFamilyIndex N) (HardFamilyIndex N) ℂ)‖ ≤
      5 * estimate / (2 * kappa) := by
  have ht : 0 ≤ vectorPerturbationSize kappa estimate := by unfold vectorPerturbationSize; positivity
  have h := perturbedPreparation_distance _ _ (hardFamilyOrthogonalPair hk he hek hN) ht (hardFamilyPreparation hk he hek hN)
  convert h using 1 <;> dsimp [vectorPerturbationSize] <;> ring

theorem hardFamilyPairedSolution_norm (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (z : BitString m) :
    ‖WithLp.toLp 2 (hardFamilyPairedSolution N kappa estimate z)‖ = 1 :=
  pairedNormalizedSolution_norm _ _ _ (hardFamily_solution_orthogonal_direction hk estimate z)
    dilatedLastDirection_norm (by linarith)

theorem hardFamilyPerturbed_solution_norm_sq (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    ‖WithLp.toLp 2 ((hardFamilyMatrix N kappa z)⁻¹ *ᵥ hardFamilyPerturbedSource N m kappa estimate)‖ ^ 2 =
      pairedSolutionNormSquared kappa estimate (commonAdjustedScale N m kappa estimate) := by
  have h := inverse_perturbedSource_norm_sq (estimate := estimate) (hardFamilyMatrix N kappa z) (hardFamilySource N m kappa estimate)
    dilatedLastDirection (by linarith : 0 < kappa) (hardFamily_direction_inverse hk z)
    dilatedLastDirection_norm (hardFamily_solution_orthogonal_direction hk estimate z)
  rw [hardFamily_solution_norm hk he hek hN z] at h
  exact h

theorem hardFamilyPerturbed_solution_factor_two (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    ‖WithLp.toLp 2 ((hardFamilyMatrix N kappa z)⁻¹ *ᵥ hardFamilyPerturbedSource N m kappa estimate)‖ / 2 ≤ estimate ∧
      estimate ≤ 2 * ‖WithLp.toLp 2 ((hardFamilyMatrix N kappa z)⁻¹ *ᵥ hardFamilyPerturbedSource N m kappa estimate)‖ := by
  have hs := commonAdjustedScale_bounds hk he hek hN
  have h := pairedSolutionNorm_factor_two (by linarith : 0 < kappa) (by linarith : 0 < estimate) hek hs.1 hs.2.1
  have hn := hardFamilyPerturbed_solution_norm_sq hk he hek hN z
  rw [← hn, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] at h
  exact h

theorem hardFamily_original_direction_probability (hk : 4 ≤ kappa) (z : BitString m) :
    (ketBra dilatedLastDirection dilatedLastDirection * pureDensity (normalizedHardFamilySolution N kappa estimate z)).trace.re = 0 := by
  rw [direction_pure_probability]
  have horth := hardFamily_solution_orthogonal_direction (N := N) hk estimate z
  have hrev : inner ℂ (WithLp.toLp 2 (dilatedLastDirection (D := HistoryBasis N)))
      (WithLp.toLp 2 ((hardFamilyMatrix N kappa z)⁻¹ *ᵥ hardFamilySource N m kappa estimate)) = 0 := by
    rw [← inner_conj_symm, horth]; simp
  change ‖inner ℂ (WithLp.toLp 2 (dilatedLastDirection (D := HistoryBasis N)))
    ((commonAdjustedScale N m kappa estimate)⁻¹ • WithLp.toLp 2 ((hardFamilyMatrix N kappa z)⁻¹ *ᵥ hardFamilySource N m kappa estimate))‖ ^ 2 = 0
  rw [inner_smul_right_eq_smul, hrev]
  simp

theorem hardFamily_paired_direction_probability (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    (25 / 61 : ℝ) ≤ (ketBra dilatedLastDirection dilatedLastDirection * pureDensity (hardFamilyPairedSolution N kappa estimate z)).trace.re := by
  rw [hardFamilyPairedSolution, pairedNormalizedSolution_direction_probability _ _ _
    (hardFamily_solution_orthogonal_direction hk estimate z) dilatedLastDirection_norm (by linarith),
    hardFamily_solution_norm hk he hek hN z]
  have hs := commonAdjustedScale_bounds hk he hek hN
  have h := pairedDirectionWeight_lower (by linarith : 0 < estimate) (by linarith [hs.2.2.1]) hs.2.1
  convert h using 1 <;> unfold pairedDirectionWeight <;> congr 1 <;> ring

end OptimalQLS.LowerBounds
