import OptimalQLS.LowerBounds.NormControlledFamily
import OptimalQLS.LowerBounds.AdjustedObservable

/-! The fixed norm-at-most-one observable and5/2304 signal in Proposition6.4. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix

def normalizedHardFamilySolution (N : ℕ) [NeZero N] {m : ℕ} (kappa estimate : ℝ) (z : BitString m) :
    HardFamilyIndex N → ℂ :=
  (commonAdjustedScale N m kappa estimate)⁻¹ •
    ((hardFamilyMatrix N kappa z)⁻¹ *ᵥ hardFamilySource N m kappa estimate)

def hardFamilyObservable {N m : ℕ} {kappa : ℝ} (hk : 4 ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) : Matrix (HardFamilyIndex N) (HardFamilyIndex N) ℂ :=
  dilatedObservable (historyObservable (historyPadding_pos hk)
    (show 2 * historyPadding kappa + m ≤ N by omega))

theorem hardFamilyObservable_hermitian {N m : ℕ} {kappa : ℝ} (hk : 4 ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) : (hardFamilyObservable hk hN).IsHermitian :=
  dilatedObservable_hermitian _ (historyObservable_hermitian _ _)

theorem hardFamilyObservable_norm_le_one {N m : ℕ} {kappa : ℝ} (hk : 4 ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) : ‖hardFamilyObservable hk hN‖ ≤ 1 := by
  rw [hardFamilyObservable, dilatedObservable_norm]
  exact historyObservable_norm_le_one _ _

theorem normalizedHardFamilySolution_norm {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    ‖WithLp.toLp 2 (normalizedHardFamilySolution N kappa estimate z)‖ = 1 := by
  have hs := commonAdjustedScale_bounds hk he hek hN
  have hpos : 0 < commonAdjustedScale N m kappa estimate := by linarith [hs.2.2.1]
  change ‖(commonAdjustedScale N m kappa estimate)⁻¹ • WithLp.toLp 2
    ((hardFamilyMatrix N kappa z)⁻¹ *ᵥ hardFamilySource N m kappa estimate)‖ = 1
  rw [norm_smul, hardFamily_solution_norm hk he hek hN z, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hpos.le), inv_mul_cancel₀ hpos.ne']

theorem hardFamily_solution_coordinates {N m : ℕ} [NeZero N] {kappa : ℝ}
    (hk : 4 ≤ kappa) (estimate : ℝ) (z : BitString m) :
    (hardFamilyMatrix N kappa z)⁻¹ *ᵥ hardFamilySource N m kappa estimate =
      Sum.elim (0 : AugmentedIndex (HistoryBasis N) → ℂ)
        (augmentedVector (identitySourceCoefficient (commonHistoryNorm N m kappa)
          (commonAdjustedScale N m kappa estimate))
          (historySourceCoefficient (commonHistoryNorm N m kappa) (commonAdjustedScale N m kappa estimate))
          (historyInverse (fixedParityProfile (N := N) (historyPadding kappa) z)
            (historyLambda kappa : ℂ) *ᵥ uniformHistorySource (historyPadding kappa))) := by
  have hp := hardFamily_augmented_inverse_pair (N := N) hk z
  rw [hardFamilyMatrix, hardFamilySource, hermitianDilation_inverse_source _ _ hp.1 hp.2,
    adjustedSource, augmentedInverse_source]

theorem real_normalizedHistorySolution_eq {N m : ℕ} [NeZero N] {kappa : ℝ}
    (hk : 4 ≤ kappa) (z : BitString m) :
    (commonHistoryNorm N m kappa)⁻¹ •
      (historyInverse (fixedParityProfile (N := N) (historyPadding kappa) z)
        (historyLambda kappa : ℂ) *ᵥ uniformHistorySource (historyPadding kappa)) =
      normalizedHistorySolution (fixedParityProfile (N := N) (historyPadding kappa) z)
        (historyPadding kappa) (historyLambda kappa) := by
  unfold normalizedHistorySolution
  rw [historySolutionNorm_eq_common hk z]
  funext i
  simp [historySolutionVector, Pi.smul_apply, RCLike.real_smul_eq_coe_mul]

/-- Exact expectation transported through the concrete direct sums and dilation. -/
theorem hardFamily_observable_expectation {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    pureExpectation (hardFamilyObservable hk hN) (normalizedHardFamilySolution N kappa estimate z) =
      (historySourceCoefficient (commonHistoryNorm N m kappa) (commonAdjustedScale N m kappa estimate) ^ 2 *
          commonHistoryNorm N m kappa ^ 2 / commonAdjustedScale N m kappa estimate ^ 2) *
        pureExpectation (historyObservable (historyPadding_pos hk)
          (show 2 * historyPadding kappa + m ≤ N by omega))
          (normalizedHistorySolution (fixedParityProfile (N := N) (historyPadding kappa) z)
            (historyPadding kappa) (historyLambda kappa)) := by
  have hY : commonHistoryNorm N m kappa ≠ 0 := by
    have h := (commonHistoryNorm_bounds hk hN).1
    linarith
  unfold hardFamilyObservable normalizedHardFamilySolution
  rw [hardFamily_solution_coordinates hk estimate z,
    dilatedObservable_normalized_expectation _ _ _ _ (commonHistoryNorm N m kappa) _ hY,
    real_normalizedHistorySolution_eq hk z]

/-- The literal fixed observable has the claimed absolute5/2304 parity signal
on the actual normalized solution of the norm-controlled Hermitian family. -/
theorem hardFamily_observable_signal {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    (5 / 2304 : ℝ) * historyLambda kappa ^ (2 * m) ≤
      paritySign z * pureExpectation (hardFamilyObservable hk hN)
        (normalizedHardFamilySolution N kappa estimate z) := by
  have hs := commonAdjustedScale_bounds hk he hek hN
  have hmass := adjusted_history_mass_lower hs.2.2.1 hs.2.2.2
  have hhistory := parity_history_observable_signal hk hN z
  have hpow : 0 ≤ historyLambda kappa ^ (2 * m) / 256 := by
    exact div_nonneg (pow_nonneg (historyLambda_nonneg hk) _) (by norm_num)
  rw [hardFamily_observable_expectation hk hN z]
  have hmass0 : 0 ≤ historySourceCoefficient (commonHistoryNorm N m kappa)
      (commonAdjustedScale N m kappa estimate) ^ 2 * commonHistoryNorm N m kappa ^ 2 /
      commonAdjustedScale N m kappa estimate ^ 2 := by linarith
  have hfirst := mul_le_mul_of_nonneg_right hmass hpow
  have hsecond := mul_le_mul_of_nonneg_left hhistory hmass0
  calc
    (5 / 2304 : ℝ) * historyLambda kappa ^ (2 * m) =
        (5 / 9 : ℝ) * (historyLambda kappa ^ (2 * m) / 256) := by ring
    _ ≤ _ := hfirst
    _ ≤ _ := hsecond
    _ = _ := by ring

end OptimalQLS.LowerBounds
