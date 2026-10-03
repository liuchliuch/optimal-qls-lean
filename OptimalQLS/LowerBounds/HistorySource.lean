import OptimalQLS.LowerBounds.HistoryGauge
import Mathlib.Algebra.BigOperators.Fin

/-! The concrete padded source is a unit vector, with no normalization premise. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix

lemma sum_fin_initial_segment {R : Type*} [AddCommMonoid R] (N ell : ℕ)
    (hell : ell ≤ N) (f : ℕ → R) :
    (∑ j : Fin N, if j.val < ell then f j.val else 0) = ∑ j : Fin ell, f j.val := by
  induction N with
  | zero =>
    have he : ell = 0 := by omega
    subst ell
    simp
  | succ N ih =>
    by_cases hle : ell ≤ N
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, if_neg (by omega : ¬N < ell), add_zero]
      exact ih hle
    · have he : ell = N + 1 := by omega
      subst ell
      apply Finset.sum_congr rfl
      intro j _
      simp [j.isLt]

theorem uniformHistorySource_norm_sq {N ell : ℕ} (hell : 0 < ell) (hN : ell ≤ N) :
    ‖WithLp.toLp 2 (uniformHistorySource (N := N) ell)‖ ^ 2 = 1 := by
  have he : (0 : ℝ) < ell := by exact_mod_cast hell
  have hs : 0 < Real.sqrt (ell : ℝ) := Real.sqrt_pos.mpr he
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  simp only [uniformHistorySource, Fintype.sum_bool, Bool.true_eq_false, and_false, if_false,
    norm_zero, zero_pow (by decide : 2 ≠ 0), and_true, zero_add]
  have heq : (∑ j : Fin N, ‖if j.val < ell then ((Real.sqrt (ell : ℝ))⁻¹ : ℂ) else 0‖ ^ 2) =
      ∑ j : Fin N, if j.val < ell then ((Real.sqrt (ell : ℝ))⁻¹) ^ 2 else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
  rw [heq, sum_fin_initial_segment N ell hN (fun _ => ((Real.sqrt (ell : ℝ))⁻¹) ^ 2)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [inv_pow, Real.sq_sqrt he.le, mul_inv_cancel₀ he.ne']

theorem uniformHistorySource_norm {N ell : ℕ} (hell : 0 < ell) (hN : ell ≤ N) :
    ‖WithLp.toLp 2 (uniformHistorySource (N := N) ell)‖ = 1 := by
  have hs := uniformHistorySource_norm_sq hell hN
  have hn := norm_nonneg (WithLp.toLp 2 (uniformHistorySource (N := N) ell))
  nlinarith

/-- The normalized source and exact inverse operator norm give the sharp
upper endpoint of the paper's source-solution norm interval. -/
theorem history_source_solution_norm_le {N ell : ℕ} [NeZero N]
    (profile : Fin N → Bool) (hell : 0 < ell) (hN : ell ≤ N)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam < 1) :
    ‖WithLp.toLp 2 (historyInverse profile (lam : ℂ) *ᵥ uniformHistorySource ell)‖ ≤
      (1 + lam) / (1 - lam) := by
  have h := (historyInverse profile (lam : ℂ)).l2_opNorm_mulVec
    (WithLp.toLp 2 (uniformHistorySource ell))
  change ‖WithLp.toLp 2 (historyInverse profile (lam : ℂ) *ᵥ uniformHistorySource ell)‖ ≤
    ‖historyInverse profile (lam : ℂ)‖ * ‖WithLp.toLp 2 (uniformHistorySource ell)‖ at h
  simpa [historyInverse_norm profile lam h0 h1, uniformHistorySource_norm hell hN] using h

end OptimalQLS.LowerBounds
