import OptimalQLS.LowerBounds.HistoryTailMass

/-!
# Actual normalized-history measurement probabilities

The outcome probabilities are sums of squared complex amplitudes of the
normalized inverse solution. Tail coordinates are injective, so the indexed
sum is the probability of the corresponding classical clock event.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix

def historySolutionVector {N : ℕ} [NeZero N] (profile : Fin N → Bool) (ell : ℕ) (lam : ℝ) :
    HistoryBasis N → ℂ := historyInverse profile (lam : ℂ) *ᵥ uniformHistorySource ell

def historySolutionNorm {N : ℕ} [NeZero N] (profile : Fin N → Bool) (ell : ℕ) (lam : ℝ) : ℝ :=
  ‖WithLp.toLp 2 (historySolutionVector profile ell lam)‖

def normalizedHistorySolution {N : ℕ} [NeZero N] (profile : Fin N → Bool)
    (ell : ℕ) (lam : ℝ) : HistoryBasis N → ℂ :=
  ((historySolutionNorm profile ell lam)⁻¹ : ℂ) • historySolutionVector profile ell lam

theorem normalizedHistorySolution_norm {N : ℕ} [NeZero N] (profile : Fin N → Bool)
    (ell : ℕ) (lam : ℝ) (hpos : 0 < historySolutionNorm profile ell lam) :
    ‖WithLp.toLp 2 (normalizedHistorySolution profile ell lam)‖ = 1 := by
  change ‖((historySolutionNorm profile ell lam)⁻¹ : ℂ) •
    WithLp.toLp 2 (historySolutionVector profile ell lam)‖ = 1
  rw [norm_smul]
  change ‖((historySolutionNorm profile ell lam)⁻¹ : ℂ)‖ * historySolutionNorm profile ell lam = 1
  simp [Complex.norm_real, Real.norm_of_nonneg hpos.le, hpos.ne']

/-- Literal Born probability of the injectively enumerated tail clock outcomes. -/
def historyTailProbability {N ell m : ℕ} [NeZero N] (profile : Fin N → Bool)
    (hell : 0 < ell) (hN : 2 * ell + m ≤ N) (lam : ℝ) : ℝ :=
  ∑ k : Fin ell, ∑ b : Bool,
    ‖normalizedHistorySolution profile ell lam (tailClock hell hN k, b)‖ ^ 2

/-- The measured normalized probability equals the scalar mass ratio. -/
theorem historyTailProbability_eq {N ell m : ℕ} [NeZero N] (profile : Fin N → Bool)
    (hfixed : ∀ j : Fin N, j.val < ell → profile j = false)
    (hell : 0 < ell) (hN : 2 * ell + m ≤ N) (lam : ℝ)
    (hplus : (1 : ℂ) + (lam : ℂ) ≠ 0) (hden : (1 : ℂ) - (lam : ℂ) ^ N ≠ 0) :
    historyTailProbability profile hell hN lam = tailAmplitudeMass hell hN lam /
      historySolutionNorm profile ell lam ^ 2 := by
  have hNe : ell ≤ N := by omega
  simp only [historyTailProbability, tailAmplitudeMass, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Fintype.sum_bool, normalizedHistorySolution, Pi.smul_apply, smul_eq_mul,
    historySolutionVector, history_solution_amplitude profile hfixed hNe lam hplus hden]
  cases hp : profile (tailClock hell hN k) <;>
    simp [hp, norm_mul, Complex.norm_real, sq_abs, mul_pow, inv_pow, div_eq_mul_inv, mul_comm]

/-- The normalized solution has unit norm and its actual clock-measurement
probability in the parity interval is at least lam^(2m)/256. -/
theorem historyTailProbability_lower {N m : ℕ} [NeZero N] {kappa : ℝ} (hk : 4 ≤ kappa)
    (hN : 2 * historyPadding kappa + m ≤ N) (profile : Fin N → Bool)
    (hfixed : ∀ j : Fin N, j.val < historyPadding kappa → profile j = false) :
    historyLambda kappa ^ (2 * m) / 256 ≤
      historyTailProbability profile (historyPadding_pos hk) hN (historyLambda kappa) := by
  have h0 := historyLambda_nonneg hk
  have h1 := historyLambda_lt_one hk
  have hplus : (1 : ℂ) + (historyLambda kappa : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show (0 : ℝ) < 1 + historyLambda kappa by linarith))
  rw [historyTailProbability_eq profile hfixed (historyPadding_pos hk) hN _ hplus
    (history_geometric_denominator_ne_zero _ h0 h1)]
  exact normalized_tail_mass_lower hk hN profile hfixed

/-- Work-bit support is preserved by normalization; it is exact, not an error
or fidelity statement. -/
theorem normalizedHistorySolution_support {N ell : ℕ} [NeZero N] (profile : Fin N → Bool)
    (hfixed : ∀ j : Fin N, j.val < ell → profile j = false) (hN : ell ≤ N)
    (lam : ℝ) (hplus : (1 : ℂ) + (lam : ℂ) ≠ 0)
    (hden : (1 : ℂ) - (lam : ℂ) ^ N ≠ 0) (j : Fin N) (b : Bool)
    (hb : b ≠ profile j) :
    normalizedHistorySolution profile ell lam (j, b) = 0 := by
  simp [normalizedHistorySolution, historySolutionVector,
    history_solution_amplitude profile hfixed hN lam hplus hden, hb]

end OptimalQLS.LowerBounds
