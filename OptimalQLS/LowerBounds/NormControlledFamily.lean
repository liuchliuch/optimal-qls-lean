import OptimalQLS.LowerBounds.FixedDirection
import OptimalQLS.LowerBounds.SumBlockEncoding

/-!
# The concrete norm-controlled Hermitian hard family (Proposition6.4)

The source and its full preparation unitary are defined without a hidden-input
argument. A common Y is taken from the all-zero history; proved gauge
invariance gives that same norm for every input string. Matrices, inverse
matrices, and exact one-signal encodings are explicit direct sums/dilations.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix

abbrev HardFamilyIndex (N : ℕ) := AugmentedIndex (HistoryBasis N) ⊕ AugmentedIndex (HistoryBasis N)

instance hardFamilyIndex_decidableEq (N : ℕ) : DecidableEq (HardFamilyIndex N) :=
  inferInstanceAs (DecidableEq ((Unit ⊕ ((Fin N × Bool) ⊕ Unit)) ⊕
    (Unit ⊕ ((Fin N × Bool) ⊕ Unit))))

def commonHistoryNorm (N m : ℕ) [NeZero N] (kappa : ℝ) : ℝ :=
  historySolutionNorm (fixedParityProfile (N := N) (historyPadding kappa) (fun _ : Fin m => false))
    (historyPadding kappa) (historyLambda kappa)

def commonAdjustedScale (N m : ℕ) [NeZero N] (kappa estimate : ℝ) : ℝ :=
  adjustedSolutionScale estimate (commonHistoryNorm N m kappa)

def hardFamilySource (N m : ℕ) [NeZero N] (kappa estimate : ℝ) : HardFamilyIndex N → ℂ :=
  Sum.elim (adjustedSource (uniformHistorySource (historyPadding kappa))
    (commonHistoryNorm N m kappa) (commonAdjustedScale N m kappa estimate)) 0

def hardFamilyMatrix (N : ℕ) [NeZero N] {m : ℕ} (kappa : ℝ) (z : BitString m) :
    Matrix (HardFamilyIndex N) (HardFamilyIndex N) ℂ :=
  hermitianDilation (augmentedMatrix
    (historyMatrix (fixedParityProfile (N := N) (historyPadding kappa) z) (historyLambda kappa : ℂ)) kappa)

def hardFamilyInverseCandidate (N : ℕ) [NeZero N] {m : ℕ} (kappa : ℝ) (z : BitString m) :
    Matrix (HardFamilyIndex N) (HardFamilyIndex N) ℂ :=
  hermitianInverseCandidate (augmentedInverse
    (historyInverse (fixedParityProfile (N := N) (historyPadding kappa) z) (historyLambda kappa : ℂ)) kappa)

theorem historyLambda_pos {kappa : ℝ} (hk : 4 ≤ kappa) : 0 < historyLambda kappa := by
  unfold historyLambda
  exact div_pos (by linarith) (by linarith)

theorem kappa_inv_abs_lt_one {kappa : ℝ} (hk : 4 ≤ kappa) : |kappa⁻¹| < 1 := by
  have hp : 0 < kappa := by linarith
  rw [abs_of_nonneg (inv_nonneg.mpr hp.le)]
  exact (inv_lt_one₀ hp).mpr (by linarith)

theorem history_inverse_pair {N : ℕ} [NeZero N] {kappa : ℝ} (hk : 4 ≤ kappa)
    (profile : Fin N → Bool) :
    historyInverse profile (historyLambda kappa : ℂ) * historyMatrix profile (historyLambda kappa : ℂ) = 1 ∧
    historyMatrix profile (historyLambda kappa : ℂ) * historyInverse profile (historyLambda kappa : ℂ) = 1 := by
  have h0 := historyLambda_nonneg hk
  have h1 := historyLambda_lt_one hk
  have hp : (1 : ℂ) + (historyLambda kappa : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show (0 : ℝ) < 1 + historyLambda kappa by linarith))
  have h := historyInverse_mul profile _ hp (history_geometric_denominator_ne_zero _ h0 h1)
  exact ⟨h, mul_eq_one_comm.mp h⟩

theorem commonHistoryNorm_bounds {N m : ℕ} [NeZero N] {kappa : ℝ}
    (hk : 4 ≤ kappa) (hN : N = 2 * historyPadding kappa + 2 * m) :
    kappa / 2 ≤ commonHistoryNorm N m kappa ∧ commonHistoryNorm N m kappa ≤ kappa := by
  exact history_source_solution_norm_bounds hk (by omega) _
    (fixedParityProfile_source (fun _ : Fin m => false))

theorem historySolutionNorm_eq_common {N m : ℕ} [NeZero N] {kappa : ℝ}
    (hk : 4 ≤ kappa) (z : BitString m) :
    historySolutionNorm (fixedParityProfile (N := N) (historyPadding kappa) z)
      (historyPadding kappa) (historyLambda kappa) = commonHistoryNorm N m kappa :=
  parity_history_solution_norm_independent hk z (fun _ => false)

theorem commonAdjustedScale_bounds {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) :
    estimate / 2 ≤ commonAdjustedScale N m kappa estimate ∧
      commonAdjustedScale N m kappa estimate ≤ 3 * estimate / 2 ∧
      3 / 2 ≤ commonAdjustedScale N m kappa estimate ∧
      commonAdjustedScale N m kappa estimate ≤ commonHistoryNorm N m kappa :=
  adjustedSolutionScale_bounds hk he hek (commonHistoryNorm_bounds hk hN).1

theorem hardFamilySource_norm {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) :
    ‖WithLp.toLp 2 (hardFamilySource N m kappa estimate)‖ = 1 := by
  have hs := commonAdjustedScale_bounds hk he hek hN
  rw [hardFamilySource, sumElim_norm_left]
  apply adjustedSource_norm hs.2.2.1 hs.2.2.2
  exact uniformHistorySource_norm (historyPadding_pos hk) (by omega)

theorem hardFamilyMatrix_hermitian {N m : ℕ} [NeZero N] (kappa : ℝ) (z : BitString m) :
    (hardFamilyMatrix N kappa z).IsHermitian := hermitianDilation_hermitian _

theorem hardFamilyMatrix_norm {N m : ℕ} [NeZero N] {kappa : ℝ}
    (hk : 4 ≤ kappa) (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    ‖hardFamilyMatrix N kappa z‖ = 1 := by
  rw [hardFamilyMatrix, hermitianDilation_norm]
  exact augmentedMatrix_norm (by linarith) _ (parity_history_operator_norms hk hN z).1

theorem hardFamily_augmented_inverse_pair {N m : ℕ} [NeZero N] {kappa : ℝ}
    (hk : 4 ≤ kappa) (z : BitString m) :
    augmentedInverse (historyInverse (fixedParityProfile (N := N) (historyPadding kappa) z)
      (historyLambda kappa : ℂ)) kappa *
      augmentedMatrix (historyMatrix (fixedParityProfile (N := N) (historyPadding kappa) z)
        (historyLambda kappa : ℂ)) kappa = 1 ∧
    augmentedMatrix (historyMatrix (fixedParityProfile (N := N) (historyPadding kappa) z)
      (historyLambda kappa : ℂ)) kappa *
      augmentedInverse (historyInverse (fixedParityProfile (N := N) (historyPadding kappa) z)
        (historyLambda kappa : ℂ)) kappa = 1 := by
  have h := history_inverse_pair hk (fixedParityProfile (N := N) (historyPadding kappa) z)
  exact ⟨augmentedInverse_mul _ _ _ (by linarith) h.1,
    augmentedMatrix_mul_inverse _ _ _ (by linarith) h.2⟩

theorem hardFamilyMatrix_inverse {N m : ℕ} [NeZero N] {kappa : ℝ}
    (hk : 4 ≤ kappa) (z : BitString m) :
    (hardFamilyMatrix N kappa z)⁻¹ = hardFamilyInverseCandidate N kappa z := by
  have h := hardFamily_augmented_inverse_pair (N := N) hk z
  exact hermitianDilation_inverse _ _ h.1 h.2

theorem hardFamilyMatrix_inverse_norm {N m : ℕ} [NeZero N] {kappa : ℝ}
    (hk : 4 ≤ kappa) (z : BitString m) : ‖(hardFamilyMatrix N kappa z)⁻¹‖ = kappa := by
  rw [hardFamilyMatrix_inverse hk z, hardFamilyInverseCandidate, hermitianInverseCandidate_norm]
  apply augmentedInverse_norm (by linarith)
  rw [historyInverse_norm _ _ (historyLambda_nonneg hk) (historyLambda_lt_one hk), historyLambda_ratio hk]

theorem hardFamily_solution_norm {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    ‖WithLp.toLp 2 ((hardFamilyMatrix N kappa z)⁻¹ *ᵥ hardFamilySource N m kappa estimate)‖ =
      commonAdjustedScale N m kappa estimate := by
  have hpair := hardFamily_augmented_inverse_pair (N := N) hk z
  have hs := commonAdjustedScale_bounds hk he hek hN
  rw [hardFamilyMatrix, hardFamilySource, hermitianDilation_solution_norm _ _ hpair.1 hpair.2]
  apply adjustedSource_inverse_norm hs.2.2.1 hs.2.2.2
  exact historySolutionNorm_eq_common hk z

/-- A single full preparation unitary, with no hidden-string argument. -/
def hardFamilyPreparation {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) : Matrix.unitaryGroup (HardFamilyIndex N) ℂ :=
  statePreparationUnitary (.inl (.inl ())) (hardFamilySource N m kappa estimate)
    (hardFamilySource_norm hk he hek hN)

theorem hardFamilyPreparation_prepares {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) (i : HardFamilyIndex N) :
    hardFamilyPreparation hk he hek hN i (.inl (.inl ())) = hardFamilySource N m kappa estimate i :=
  statePreparationUnitary_prepares _ _ _ i

/-- Exact constant-signal encoding of the whole Hermitian augmented family. -/
def hardFamilyEncoding {N m : ℕ} [NeZero N] {kappa : ℝ} (hk : 4 ≤ kappa) (z : BitString m) :
    Matrix.unitaryGroup (Bool × HardFamilyIndex N) ℂ :=
  dilationEncoding (sumEncoding (1 : Matrix.unitaryGroup (Bool × Unit) ℂ)
    (sumEncoding (historyBlockEncoding (fixedParityProfile (N := N) (historyPadding kappa) z)
      (historyLambda kappa) (historyLambda_pos hk)) (scalarEncoding kappa⁻¹ (kappa_inv_abs_lt_one hk))))

theorem hardFamilyEncoding_exact {N m : ℕ} [NeZero N] {kappa : ℝ}
    (hk : 4 ≤ kappa) (z : BitString m) :
    OptimalQLS.IsBlockEncoding false 1 0 (hardFamilyEncoding (N := N) hk z) (hardFamilyMatrix N kappa z) := by
  unfold hardFamilyEncoding hardFamilyMatrix augmentedMatrix
  apply dilationEncoding_exact
  apply sumEncoding_exact
  · exact identityEncoding_exact false
  · apply sumEncoding_exact
    · exact historyBlockEncoding_exact _ _ _
    · exact scalarEncoding_exact _ _

/-- The common direction has norm1 and eigenvalue1/kappa on every family member. -/
theorem hardFamily_fixed_direction {N m : ℕ} [NeZero N] (kappa : ℝ) (z : BitString m) :
    ‖WithLp.toLp 2 (dilatedLastDirection (D := HistoryBasis N))‖ = 1 ∧
    hardFamilyMatrix N kappa z *ᵥ dilatedLastDirection = kappa⁻¹ • dilatedLastDirection :=
  ⟨dilatedLastDirection_norm, dilatedLastDirection_eigen _ _⟩

theorem hardFamily_source_orthogonal_direction {N m : ℕ} [NeZero N] (kappa estimate : ℝ) :
    inner ℂ (WithLp.toLp 2 (hardFamilySource N m kappa estimate))
      (WithLp.toLp 2 (dilatedLastDirection (D := HistoryBasis N))) = 0 :=
  dilatedLastDirection_orthogonal_left _ _ _

theorem hardFamily_solution_orthogonal_direction {N m : ℕ} [NeZero N] {kappa : ℝ}
    (hk : 4 ≤ kappa) (estimate : ℝ) (z : BitString m) :
    inner ℂ (WithLp.toLp 2 ((hardFamilyMatrix N kappa z)⁻¹ *ᵥ hardFamilySource N m kappa estimate))
      (WithLp.toLp 2 (dilatedLastDirection (D := HistoryBasis N))) = 0 := by
  have hp := hardFamily_augmented_inverse_pair (N := N) hk z
  rw [hardFamilyMatrix, hardFamilySource, hermitianDilation_inverse_source _ _ hp.1 hp.2,
    adjustedSource, augmentedInverse_source]
  exact dilatedLastDirection_orthogonal_right _ _ _

theorem hardFamily_dimension (N : ℕ) : Fintype.card (HardFamilyIndex N) = 4 * N + 4 := by
  simp [HardFamilyIndex, AugmentedIndex, HistoryBasis]
  omega

end OptimalQLS.LowerBounds
