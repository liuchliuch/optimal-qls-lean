import OptimalQLS.LowerBounds.HistoryProbability

/-!
# The fixed-m cyclic parity-history family (Section6, Definition6.2/Lemma6.3)

This interface uses one fixed clock dimension for all Boolean input strings,
with no dependent-dimension mismatch. Operator norms concern actual matrices;
solution norms concern their actual nonsingular inverses; the tail lower bound
concerns normalized Born probabilities. All quantitative facts are derived
from the concrete transition list and previous finite calculations.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix

/-- Prefix parity for the literal transition sequence, on a separately fixed clock. -/
def fixedParityProfile {N m : ℕ} (ell : ℕ) (z : BitString m) : Fin N → Bool :=
  fun j => xorFold ((parityHistoryGates ell (List.ofFn z)).take j.val)

theorem fixedParityProfile_source {N m ell : ℕ} (z : BitString m)
    (j : Fin N) (hj : j.val < ell) : fixedParityProfile ell z j = false :=
  parityHistoryGates_initial_prefix (List.ofFn z) hj

theorem fixedParityProfile_tail {N m ell : ℕ} (hell : 0 < ell)
    (hN : 2 * ell + m ≤ N) (z : BitString m) (k : Fin ell) :
    fixedParityProfile ell z (tailClock hell hN k) = xorFold (List.ofFn z) := by
  have ht := parityHistoryGates_tail_prefix (List.ofFn z) (Nat.le_of_lt k.isLt)
  have hi : ell - 1 + (List.ofFn z).length + k.val = (tailClock hell hN k).val := by
    simp only [List.length_ofFn, tailClock]
    omega
  simpa only [hi, fixedParityProfile] using ht

/-- This fixed-dimension matrix has exactly the paper's controlled-X transition
at every clock, including the cyclic wraparound transition. -/
theorem fixedParityProfile_transition {N m ell : ℕ} [NeZero N] (hell : 0 < ell)
    (hN : N = 2 * ell + 2 * m) (z : BitString m) (j : Fin N) (b : Bool) :
    historyPermutation (fixedParityProfile ell z) (j, b) =
      (j + 1, Bool.xor b ((parityHistoryGates ell (List.ofFn z)).get ⟨j.val, by
        rw [parityHistoryGates_length (by omega), List.length_ofFn, ← hN]
        exact j.isLt⟩)) := by
  have hlen : (parityHistoryGates ell (List.ofFn z)).length = N := by
    rw [parityHistoryGates_length (by omega), List.length_ofFn, hN]
  cases hlen
  exact historyPermutation_prefixProfile_apply _ (parityHistoryGates_xor ell (List.ofFn z)) j b

/-- The claimed clock length is positive for every admissible kappa. -/
theorem parity_history_length_pos {kappa : ℝ} (hk : 4 ≤ kappa) (m : ℕ) :
    0 < 2 * historyPadding kappa + 2 * m := by
  have h := historyPadding_pos hk
  omega

/-- Exact operator norm identities from Lemma6.3, with the paper's kappa. -/
theorem parity_history_operator_norms {N m : ℕ} [NeZero N] {kappa : ℝ}
    (hk : 4 ≤ kappa) (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    ‖historyMatrix (fixedParityProfile (N := N) (historyPadding kappa) z)
      (historyLambda kappa : ℂ)‖ = 1 ∧
    ‖(historyMatrix (fixedParityProfile (N := N) (historyPadding kappa) z)
      (historyLambda kappa : ℂ))⁻¹‖ = kappa := by
  have heven : Even N := by rw [hN]; exact ⟨historyPadding kappa + m, by omega⟩
  have h0 := historyLambda_nonneg hk
  have h1 := historyLambda_lt_one hk
  have hp : (1 : ℂ) + (historyLambda kappa : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show (0 : ℝ) < 1 + historyLambda kappa by linarith))
  constructor
  · exact historyMatrix_norm heven _ _ h0
  · rw [historyMatrix_inv _ _ hp (history_geometric_denominator_ne_zero _ h0 h1),
      historyInverse_norm _ _ h0 h1, historyLambda_ratio hk]

/-- The source is genuinely normalized, for the literal clock dimension. -/
theorem parity_history_source_norm {N m : ℕ} {kappa : ℝ}
    (hk : 4 ≤ kappa) (hN : N = 2 * historyPadding kappa + 2 * m) :
    ‖WithLp.toLp 2 (uniformHistorySource (N := N) (historyPadding kappa))‖ = 1 :=
  uniformHistorySource_norm (historyPadding_pos hk) (by omega)

/-- The actual inverse-source norm is between kappa/2 and kappa. -/
theorem parity_history_solution_norm_bounds {N m : ℕ} [NeZero N] {kappa : ℝ}
    (hk : 4 ≤ kappa) (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    kappa / 2 ≤ ‖WithLp.toLp 2
      ((historyMatrix (fixedParityProfile (N := N) (historyPadding kappa) z)
        (historyLambda kappa : ℂ))⁻¹ *ᵥ uniformHistorySource (historyPadding kappa))‖ ∧
    ‖WithLp.toLp 2
      ((historyMatrix (fixedParityProfile (N := N) (historyPadding kappa) z)
        (historyLambda kappa : ℂ))⁻¹ *ᵥ uniformHistorySource (historyPadding kappa))‖ ≤ kappa := by
  have h0 := historyLambda_nonneg hk
  have h1 := historyLambda_lt_one hk
  have hp : (1 : ℂ) + (historyLambda kappa : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show (0 : ℝ) < 1 + historyLambda kappa by linarith))
  rw [historyMatrix_inv _ _ hp (history_geometric_denominator_ne_zero _ h0 h1)]
  exact history_source_solution_norm_bounds hk (by omega) _ (fixedParityProfile_source z)

/-- The exact solution norm agrees for every pair of hidden m-bit strings. -/
theorem parity_history_solution_norm_independent {N m : ℕ} [NeZero N] {kappa : ℝ}
    (hk : 4 ≤ kappa) (z z' : BitString m) :
    historySolutionNorm (fixedParityProfile (N := N) (historyPadding kappa) z)
      (historyPadding kappa) (historyLambda kappa) =
    historySolutionNorm (fixedParityProfile (N := N) (historyPadding kappa) z')
      (historyPadding kappa) (historyLambda kappa) := by
  have h0 := historyLambda_nonneg hk
  have h1 := historyLambda_lt_one hk
  have hp : (1 : ℂ) + (historyLambda kappa : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show (0 : ℝ) < 1 + historyLambda kappa by linarith))
  have hd := history_geometric_denominator_ne_zero (N := N) _ h0 h1
  unfold historySolutionNorm historySolutionVector
  rw [history_solution_norm_independent _ (fixedParityProfile_source z) _ hp hd,
    history_solution_norm_independent _ (fixedParityProfile_source z') _ hp hd]

/-- The normalized solution has unit norm, so its Born weights are probabilities. -/
theorem parity_history_normalized_norm {N m : ℕ} [NeZero N] {kappa : ℝ}
    (hk : 4 ≤ kappa) (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    ‖WithLp.toLp 2 (normalizedHistorySolution
      (fixedParityProfile (N := N) (historyPadding kappa) z)
      (historyPadding kappa) (historyLambda kappa))‖ = 1 := by
  apply normalizedHistorySolution_norm
  have h := history_source_solution_norm_lower hk (show historyPadding kappa ≤ N by omega)
    (fixedParityProfile (historyPadding kappa) z) (fixedParityProfile_source z)
  change kappa / 2 ≤ historySolutionNorm _ _ _ at h
  linarith

/-- The actual tail-measurement probability is at least lambda^(2m)/256. -/
theorem parity_history_tail_probability {N m : ℕ} [NeZero N] {kappa : ℝ}
    (hk : 4 ≤ kappa) (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    historyLambda kappa ^ (2 * m) / 256 ≤
      historyTailProbability (fixedParityProfile (N := N) (historyPadding kappa) z)
        (historyPadding_pos hk) (show 2 * historyPadding kappa + m ≤ N by omega)
        (historyLambda kappa) :=
  historyTailProbability_lower hk (by omega) _ (fixedParityProfile_source z)

/-- On every tail clock outcome, the opposite-parity work amplitude vanishes
exactly. This is the deterministic parity-storage assertion in Lemma6.3. -/
theorem parity_history_tail_work_bit {N m : ℕ} [NeZero N] {kappa : ℝ}
    (hk : 4 ≤ kappa) (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m)
    (k : Fin (historyPadding kappa)) :
    normalizedHistorySolution (fixedParityProfile (N := N) (historyPadding kappa) z)
      (historyPadding kappa) (historyLambda kappa)
      (tailClock (historyPadding_pos hk) (show 2 * historyPadding kappa + m ≤ N by omega) k,
        !(xorFold (List.ofFn z))) = 0 := by
  have h0 := historyLambda_nonneg hk
  have h1 := historyLambda_lt_one hk
  have hp : (1 : ℂ) + (historyLambda kappa : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show (0 : ℝ) < 1 + historyLambda kappa by linarith))
  apply normalizedHistorySolution_support _ (fixedParityProfile_source z) (by omega) _ hp
    (history_geometric_denominator_ne_zero _ h0 h1)
  rw [fixedParityProfile_tail]
  exact Bool.not_ne_self _

end OptimalQLS.LowerBounds
