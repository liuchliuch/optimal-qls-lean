import OptimalQLS.LowerBounds.HistoryAmplitudes
import OptimalQLS.LowerBounds.HistoryPowerBounds
import Mathlib.Data.Fin.Rev

/-! Exact and lower-bounded finite clock-amplitude sums. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Fin.NatCast
namespace OptimalQLS.LowerBounds
open Matrix

lemma sum_reverse_powers (lam : ℝ) (ell : ℕ) :
    (∑ i : Fin ell, lam ^ (ell - 1 - i.val)) = ∑ i : Fin ell, lam ^ i.val := by
  calc
    _ = ∑ i : Fin ell, lam ^ (Fin.rev i).val := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      simp only [Fin.rev]
      omega
    _ = _ := Equiv.sum_comp Fin.revPerm (fun i : Fin ell => lam ^ i.val)

lemma historyAmplitude_nonneg {N ell : ℕ} [NeZero N]
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam < 1) (j : Fin N) :
    0 ≤ historyAmplitude ell lam j := by
  have hp : 0 ≤ 1 - lam ^ N := by
    have h := pow_lt_one₀ h0 h1 (NeZero.ne N)
    linarith
  apply mul_nonneg
  · apply div_nonneg (by linarith)
    exact mul_nonneg (Real.sqrt_nonneg _) hp
  · exact Finset.sum_nonneg (fun _ _ => pow_nonneg h0 _)

/-- No modular wraparound occurs in any source-to-tail exponent. -/
lemma history_tail_exponent {N ell : ℕ} [NeZero N] (hell : 0 < ell) (hN : ell ≤ N)
    (j : Fin N) (hj : ell - 1 ≤ j.val) (i : Fin ell) :
    (j - (i.val : Fin N)).val = (j.val + 1 - ell) + (ell - 1 - i.val) := by
  have hcast : (i.val : Fin N).val = i.val := Fin.val_cast_of_lt (i.isLt.trans_le hN)
  have hle : (i.val : Fin N) ≤ j := by
    apply Fin.le_iff_val_le_val.mpr
    rw [hcast]
    omega
  rw [Fin.sub_val_of_le hle, hcast]
  omega

/-- Exact geometric form of every amplitude after the source interval. -/
theorem historyAmplitude_tail_exact {N ell : ℕ} [NeZero N] (hell : 0 < ell) (hN : ell ≤ N)
    (lam : ℝ) (j : Fin N) (hj : ell - 1 ≤ j.val) :
    historyAmplitude ell lam j =
      lam ^ (j.val + 1 - ell) *
        ((1 + lam) / (Real.sqrt (ell : ℝ) * (1 - lam ^ N))) *
          ∑ i : Fin ell, lam ^ i.val := by
  unfold historyAmplitude
  have hs : (∑ i : Fin ell, lam ^ (j - (i.val : Fin N)).val) =
      lam ^ (j.val + 1 - ell) * ∑ i : Fin ell, lam ^ i.val := by
    simp only [history_tail_exponent hell hN j hj, pow_add, ← Finset.mul_sum]
    rw [sum_reverse_powers]
  rw [hs]
  ring

/-- Tail amplitudes decay exactly by powers of lam from the last source clock. -/
theorem historyAmplitude_tail_ratio {N ell : ℕ} [NeZero N] (hell : 0 < ell) (hN : ell ≤ N)
    (lam : ℝ) (j : Fin N) (hj : ell - 1 ≤ j.val) :
    historyAmplitude ell lam j = lam ^ (j.val + 1 - ell) *
      historyAmplitude (N := N) ell lam ⟨ell - 1, by omega⟩ := by
  rw [historyAmplitude_tail_exact hell hN lam j hj,
    historyAmplitude_tail_exact hell hN lam ⟨ell - 1, by omega⟩ (by simp)]
  have he : ell - 1 + 1 - ell = 0 := by omega
  simp only [he, pow_zero, one_mul]
  ring

/-- A lower bound matching the displayed tail-amplitude inequality in the paper. -/
theorem historyAmplitude_tail_lower {N ell : ℕ} [NeZero N] (hell : 0 < ell) (hN : ell ≤ N)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam < 1) (j : Fin N) (hj : ell - 1 ≤ j.val) :
    lam ^ (j.val + 1 - ell) * ((1 + lam) / (1 - lam)) /
      Real.sqrt (ell : ℝ) * (1 - lam ^ ell) ≤ historyAmplitude ell lam j := by
  have he : (0 : ℝ) < ell := by exact_mod_cast hell
  have hs : 0 < Real.sqrt (ell : ℝ) := Real.sqrt_pos.mpr he
  have hd : 0 < 1 - lam ^ N := by
    have h := pow_lt_one₀ h0 h1 (NeZero.ne N)
    linarith
  have hdle : 1 - lam ^ N ≤ 1 := by linarith [pow_nonneg h0 N]
  have hgap : 0 < 1 - lam := by linarith
  have hnum : 0 ≤ lam ^ (j.val + 1 - ell) * ((1 + lam) / (1 - lam)) /
      Real.sqrt (ell : ℝ) * (1 - lam ^ ell) := by
    have hpe : 0 ≤ 1 - lam ^ ell := by
      have h : lam ^ ell ≤ 1 := pow_le_one₀ h0 h1.le
      linarith
    positivity
  rw [historyAmplitude_tail_exact hell hN lam j hj, Fin.sum_univ_eq_sum_range,
    real_geometric_sum lam ell h1.ne]
  have heq : lam ^ (j.val + 1 - ell) *
      ((1 + lam) / (Real.sqrt (ell : ℝ) * (1 - lam ^ N))) *
      ((1 - lam ^ ell) / (1 - lam)) =
      (lam ^ (j.val + 1 - ell) * ((1 + lam) / (1 - lam)) /
        Real.sqrt (ell : ℝ) * (1 - lam ^ ell)) / (1 - lam ^ N) := by
        simp only [div_eq_mul_inv, _root_.mul_inv_rev]
        ring
  rw [heq]
  apply (le_div_iff₀ hd).mpr
  exact mul_le_of_le_one_right hnum hdle

/-- Squared solution norm is precisely the sum of the scalar clock amplitudes. -/
theorem history_solution_norm_sq_amplitudes {N ell : ℕ} [NeZero N] (profile : Fin N → Bool)
    (hfixed : ∀ j : Fin N, j.val < ell → profile j = false) (hN : ell ≤ N)
    (lam : ℝ) (hplus : (1 : ℂ) + (lam : ℂ) ≠ 0)
    (hden : (1 : ℂ) - (lam : ℂ) ^ N ≠ 0) :
    ‖WithLp.toLp 2 (historyInverse profile (lam : ℂ) *ᵥ uniformHistorySource ell)‖ ^ 2 =
      ∑ j : Fin N, (historyAmplitude ell lam j) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fintype.sum_bool]
  simp only [history_solution_amplitude profile hfixed hN lam hplus hden]
  cases hp : profile j <;> simp [hp, Complex.norm_real, sq_abs]

end OptimalQLS.LowerBounds
