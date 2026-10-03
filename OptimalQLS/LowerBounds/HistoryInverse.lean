import OptimalQLS.LowerBounds.HistoryGates
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Exact finite geometric inverse of the cyclic history matrix

All matrix inverses in this file are proved from explicit finite sums and the
already-proved period of the concrete permutation. No inverse-existence or
geometric-resolvent certificate is assumed.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Explicit candidate for `(I - lam B)⁻¹` for a period-N matrix. -/
def cyclicInverse (B : Matrix n n ℂ) (lam : ℂ) (N : ℕ) : Matrix n n ℂ :=
  (1 - lam ^ N)⁻¹ • ∑ k ∈ Finset.range N, (lam • B) ^ k

theorem cyclicInverse_mul (B : Matrix n n ℂ) (lam : ℂ) (N : ℕ)
    (hperiod : B ^ N = 1) (hden : 1 - lam ^ N ≠ 0) :
    cyclicInverse B lam N * (1 - lam • B) = 1 := by
  rw [cyclicInverse, smul_mul_assoc, geom_sum_mul_neg, smul_pow, hperiod]
  have heq : (1 : Matrix n n ℂ) - lam ^ N • 1 = (1 - lam ^ N) • (1 : Matrix n n ℂ) := by
    rw [sub_smul, one_smul]
  rw [heq, smul_smul]
  simp [hden]

theorem mul_cyclicInverse (B : Matrix n n ℂ) (lam : ℂ) (N : ℕ)
    (hperiod : B ^ N = 1) (hden : 1 - lam ^ N ≠ 0) :
    (1 - lam • B) * cyclicInverse B lam N = 1 := by
  rw [cyclicInverse, mul_smul_comm, mul_neg_geom_sum, smul_pow, hperiod]
  have heq : (1 : Matrix n n ℂ) - lam ^ N • 1 = (1 - lam ^ N) • (1 : Matrix n n ℂ) := by
    rw [sub_smul, one_smul]
  rw [heq, smul_smul]
  simp [hden]

theorem inv_eq_cyclicInverse (B : Matrix n n ℂ) (lam : ℂ) (N : ℕ)
    (hperiod : B ^ N = 1) (hden : 1 - lam ^ N ≠ 0) :
    (1 - lam • B)⁻¹ = cyclicInverse B lam N :=
  Matrix.inv_eq_left_inv (cyclicInverse_mul B lam N hperiod hden)

/-- The paper's normalized non-Hermitian cyclic history matrix. -/
def historyMatrix {N : ℕ} [NeZero N] (profile : Fin N → Bool) (lam : ℂ) :
    Matrix (HistoryBasis N) (HistoryBasis N) ℂ :=
  (1 + lam)⁻¹ • (1 - lam • historyStep profile)

/-- Explicit, correctly scaled inverse of the normalized history matrix. -/
def historyInverse {N : ℕ} [NeZero N] (profile : Fin N → Bool) (lam : ℂ) :
    Matrix (HistoryBasis N) (HistoryBasis N) ℂ :=
  (1 + lam) • cyclicInverse (historyStep profile) lam N

theorem historyInverse_mul {N : ℕ} [NeZero N] (profile : Fin N → Bool)
    (lam : ℂ) (hplus : 1 + lam ≠ 0) (hden : 1 - lam ^ N ≠ 0) :
    historyInverse profile lam * historyMatrix profile lam = 1 := by
  rw [historyInverse, historyMatrix, smul_mul_assoc, mul_smul_comm,
    cyclicInverse_mul _ _ _ (historyStep_pow_length profile) hden, smul_smul]
  simp [hplus]

theorem historyMatrix_inv {N : ℕ} [NeZero N] (profile : Fin N → Bool)
    (lam : ℂ) (hplus : 1 + lam ≠ 0) (hden : 1 - lam ^ N ≠ 0) :
    (historyMatrix profile lam)⁻¹ = historyInverse profile lam :=
  Matrix.inv_eq_left_inv (historyInverse_mul profile lam hplus hden)

/-- The denominator is nonzero throughout the real parameter range used by
the parity-history construction. -/
theorem history_geometric_denominator_ne_zero {N : ℕ} [NeZero N]
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) :
    1 - (lam : ℂ) ^ N ≠ 0 := by
  have hp : lam ^ N < 1 := pow_lt_one₀ hlam0 hlam1 (NeZero.ne N)
  have hr : 1 - lam ^ N ≠ 0 := by linarith
  exact_mod_cast hr

end OptimalQLS.LowerBounds
