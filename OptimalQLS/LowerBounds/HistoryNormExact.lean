import OptimalQLS.LowerBounds.HistoryEigenvectors

/-! The even-cycle alternating eigenvector proves the exact history norm. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix

lemma pow_mod_of_pow_eq_one {M : Type*} [Monoid M] (a : M) (N k : ℕ) (h : a ^ N = 1) :
    a ^ (k % N) = a ^ k := by
  have heq := congrArg (fun t : ℕ => a ^ t) (Nat.mod_add_div k N)
  simpa [pow_add, pow_mul, h] using heq

def alternatingClock {N : ℕ} (b : HistoryBasis N) : ℂ := (-1) ^ b.1.val

theorem alternatingClock_succ {N : ℕ} [NeZero N] (hN : Even N)
    (j : Fin N) (b c : Bool) :
    alternatingClock (j + 1, b) = -alternatingClock (j, c) := by
  simp only [alternatingClock, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  rw [pow_mod_of_pow_eq_one (-1 : ℂ) N (j.val + 1) hN.neg_one_pow, pow_succ]
  ring

theorem alternatingClock_historyPermutation {N : ℕ} [NeZero N] (hN : Even N)
    (profile : Fin N → Bool) (b : HistoryBasis N) :
    alternatingClock (historyPermutation profile b) = -alternatingClock b := by
  rcases b with ⟨j, b⟩
  rw [historyPermutation_apply]
  exact alternatingClock_succ hN j _ b

theorem alternatingClock_historyPermutation_inv {N : ℕ} [NeZero N] (hN : Even N)
    (profile : Fin N → Bool) (b : HistoryBasis N) :
    alternatingClock ((historyPermutation profile)⁻¹ b) = -alternatingClock b := by
  have h := alternatingClock_historyPermutation hN profile ((historyPermutation profile)⁻¹ b)
  simp only [Equiv.Perm.apply_inv_self] at h
  linear_combination h

theorem historyStep_mulVec_alternating {N : ℕ} [NeZero N] (hN : Even N)
    (profile : Fin N → Bool) :
    historyStep profile *ᵥ alternatingClock = -alternatingClock := by
  rw [historyStep, Matrix.permMatrixHom_apply, Matrix.permMatrix_mulVec]
  funext b
  exact alternatingClock_historyPermutation_inv hN profile b

theorem historyMatrix_mulVec_alternating {N : ℕ} [NeZero N] (hN : Even N)
    (profile : Fin N → Bool) (lam : ℂ) (hplus : 1 + lam ≠ 0) :
    historyMatrix profile lam *ᵥ alternatingClock = alternatingClock := by
  rw [historyMatrix, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, historyStep_mulVec_alternating hN profile]
  funext b
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
  field_simp
  ring

/-- Exact norm one for every clock-profile gauge on an even clock. -/
theorem historyMatrix_norm {N : ℕ} [NeZero N] (hN : Even N) (profile : Fin N → Bool)
    (lam : ℝ) (h0 : 0 ≤ lam) :
    ‖historyMatrix profile (lam : ℂ)‖ = 1 := by
  apply le_antisymm (historyMatrix_norm_le_one profile lam h0)
  have hplus : (1 : ℂ) + (lam : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show (0 : ℝ) < 1 + lam by linarith))
  have hv : (alternatingClock : HistoryBasis N → ℂ) ≠ 0 := by
    intro h
    have hh := congrFun h (0, false)
    simpa [alternatingClock] using hh
  have heigen : historyMatrix profile (lam : ℂ) *ᵥ alternatingClock =
      (1 : ℂ) • alternatingClock := by
    simpa using historyMatrix_mulVec_alternating hN profile (lam : ℂ) hplus
  simpa using eigenvalue_norm_le_matrix_norm (historyMatrix profile (lam : ℂ))
    alternatingClock hv 1 heigen

end OptimalQLS.LowerBounds
