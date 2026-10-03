import OptimalQLS.LowerBounds.HistorySource

/-!
# Exact clock amplitudes of the inverse-history solution

The solution formula is derived from the concrete finite geometric matrix
inverse and reversible clock action. All profile dependence is a work-bit
permutation; the scalar clock amplitudes are independent of the hidden input.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Fin.NatCast
namespace OptimalQLS.LowerBounds
open Matrix

@[simp] theorem clockShift_inv_pow_apply {N : ℕ} [NeZero N] (k : ℕ)
    (j : Fin N) (b : Bool) :
    (clockShift N ^ k)⁻¹ (j, b) = (j - (k : Fin N), b) := by
  have h : (clockShift N ^ k) (j - (k : Fin N), b) = (j, b) := by
    simp
  exact (Equiv.symm_apply_eq (clockShift N ^ k)).mpr h.symm

@[simp] theorem historyStep_zero_pow {N : ℕ} [NeZero N] (k : ℕ) :
    historyStep (fun _ : Fin N => false) ^ k =
      Matrix.permMatrixHom (R := ℂ) (clockShift N ^ k) := by
  rw [historyStep, ← map_pow]
  congr 1
  simp [historyPermutation]

/-- A power of the actual clock unitary shifts amplitudes backwards by k. -/
theorem historyStep_zero_pow_mulVec {N : ℕ} [NeZero N] (k : ℕ)
    (v : HistoryBasis N → ℂ) (j : Fin N) (b : Bool) :
    ((historyStep (fun _ : Fin N => false) ^ k) *ᵥ v) (j, b) =
      v (j - (k : Fin N), b) := by
  rw [historyStep_zero_pow, Matrix.permMatrixHom_apply, Matrix.permMatrix_mulVec]
  change v ((clockShift N ^ k)⁻¹ (j, b)) = _
  rw [clockShift_inv_pow_apply]

/-- Coordinate form of the finite geometric inverse, for any source vector. -/
theorem historyInverse_zero_mulVec {N : ℕ} [NeZero N]
    (lam : ℂ) (v : HistoryBasis N → ℂ) (j : Fin N) (b : Bool) :
    (historyInverse (fun _ : Fin N => false) lam *ᵥ v) (j, b) =
      ((1 + lam) / (1 - lam ^ N)) *
        ∑ k : Fin N, lam ^ k.val * v (j - k, b) := by
  simp only [historyInverse, cyclicInverse, smul_smul, Matrix.smul_mulVec,
    Matrix.sum_mulVec, smul_pow, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  simp only [historyStep_zero_pow_mulVec]
  rw [← Fin.sum_univ_eq_sum_range]
  simp [div_eq_mul_inv]

/-- Scalar clock amplitude of the canonical source in the paper's formula. -/
def historyAmplitude {N : ℕ} [NeZero N] (ell : ℕ) (lam : ℝ) (j : Fin N) : ℝ :=
  (1 + lam) / (Real.sqrt (ell : ℝ) * (1 - lam ^ N)) *
    ∑ i : Fin ell, lam ^ (j - (i.val : Fin N)).val

/-- Reindex the inverse's time-sum by the source clock position. -/
theorem history_time_sum_reindex {N : ℕ} [NeZero N]
    (lam : ℂ) (v : HistoryBasis N → ℂ) (j : Fin N) (b : Bool) :
    (∑ k : Fin N, lam ^ k.val * v (j - k, b)) =
      ∑ i : Fin N, lam ^ (j - i).val * v (i, b) := by
  have h := Equiv.sum_comp (Equiv.subLeft j)
    (fun k : Fin N => lam ^ k.val * v (j - k, b))
  simpa using h.symm

/-- The canonical solution never leaves the work-zero sector. -/
theorem historyInverse_zero_source_true {N ell : ℕ} [NeZero N]
    (lam : ℂ) (j : Fin N) :
    (historyInverse (fun _ : Fin N => false) lam *ᵥ uniformHistorySource ell) (j, true) = 0 := by
  rw [historyInverse_zero_mulVec]
  simp [uniformHistorySource]

/-- Exact scalar amplitude formula for the work-zero sector. -/
theorem historyInverse_zero_source_false {N ell : ℕ} [NeZero N] (hN : ell ≤ N)
    (lam : ℝ) (j : Fin N) :
    (historyInverse (fun _ : Fin N => false) (lam : ℂ) *ᵥ uniformHistorySource ell) (j, false) =
      (historyAmplitude ell lam j : ℂ) := by
  rw [historyInverse_zero_mulVec, history_time_sum_reindex]
  simp only [uniformHistorySource, and_true]
  have heq : (∑ i : Fin N, (lam : ℂ) ^ (j - i).val *
      (if i.val < ell then ((Real.sqrt (ell : ℝ))⁻¹ : ℂ) else 0)) =
      ((Real.sqrt (ell : ℝ))⁻¹ : ℂ) *
        ∑ i : Fin ell, (lam : ℂ) ^ (j - (i.val : Fin N)).val := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ i : Fin N, if i.val < ell then
          ((Real.sqrt (ell : ℝ))⁻¹ : ℂ) * (lam : ℂ) ^ (j - (i.val : Fin N)).val else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [Fin.cast_val_eq_self]
        split_ifs <;> ring
      _ = _ := sum_fin_initial_segment N ell hN
        (fun t : ℕ => ((Real.sqrt (ell : ℝ))⁻¹ : ℂ) * (lam : ℂ) ^ (j - (t : Fin N)).val)
  rw [heq]
  simp only [historyAmplitude, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_add,
    Complex.ofReal_one, Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_sum,
    div_eq_mul_inv, _root_.mul_inv_rev, Complex.ofReal_inv]
  ring

/-- Exact support statement: at each clock only the gauge work bit can occur. -/
theorem history_solution_amplitude {N ell : ℕ} [NeZero N] (profile : Fin N → Bool)
    (hfixed : ∀ j : Fin N, j.val < ell → profile j = false) (hN : ell ≤ N)
    (lam : ℝ) (hplus : (1 : ℂ) + (lam : ℂ) ≠ 0)
    (hden : (1 : ℂ) - (lam : ℂ) ^ N ≠ 0) (j : Fin N) (b : Bool) :
    (historyInverse profile (lam : ℂ) *ᵥ uniformHistorySource ell) (j, b) =
      if b = profile j then (historyAmplitude ell lam j : ℂ) else 0 := by
  rw [history_solution_gauge profile hfixed (lam : ℂ) hplus hden, gaugeMatrix_mulVec]
  cases hp : profile j <;> cases b <;>
    simp [hp, historyInverse_zero_source_false hN, historyInverse_zero_source_true]

end OptimalQLS.LowerBounds
