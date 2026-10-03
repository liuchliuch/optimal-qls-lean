import OptimalQLS.LowerBounds.HistoryNorms

/-! Explicit eigenvectors certify sharpness of cyclic-resolvent norm bounds. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A concrete nonzero eigenvector bounds the actual Euclidean operator norm. -/
theorem eigenvalue_norm_le_matrix_norm (A : Matrix n n ℂ) (v : n → ℂ)
    (hv : v ≠ 0) (a : ℂ) (heigen : A *ᵥ v = a • v) :
    ‖a‖ ≤ ‖A‖ := by
  let vE : EuclideanSpace ℂ n := WithLp.toLp 2 v
  have hvE : vE ≠ 0 := by
    intro h
    apply hv
    exact congrArg (fun x : EuclideanSpace ℂ n => (x : n → ℂ)) h
  have hb := A.l2_opNorm_mulVec vE
  change ‖WithLp.toLp 2 (A *ᵥ v)‖ ≤ ‖A‖ * ‖vE‖ at hb
  rw [heigen] at hb
  change ‖a • vE‖ ≤ ‖A‖ * ‖vE‖ at hb
  rw [norm_smul] at hb
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hvE)).mp hb

/-- Inverting a genuine matrix eigenvector uses the proved inverse equation. -/
theorem leftInverse_mulVec_eigen (A C : Matrix n n ℂ) (hCA : C * A = 1)
    (v : n → ℂ) (a : ℂ) (ha : a ≠ 0) (heigen : A *ᵥ v = a • v) :
    C *ᵥ v = a⁻¹ • v := by
  have hv : a • (C *ᵥ v) = v := by
    rw [← Matrix.mulVec_smul, ← heigen, Matrix.mulVec_mulVec, hCA, Matrix.one_mulVec]
  calc
    C *ᵥ v = a⁻¹ • (a • (C *ᵥ v)) := by simp [ha]
    _ = a⁻¹ • v := by rw [hv]

@[simp] theorem historyStep_mulVec_constant {N : ℕ} [NeZero N]
    (profile : Fin N → Bool) (a : ℂ) :
    historyStep profile *ᵥ (fun _ => a) = (fun _ => a) := by
  simp [historyStep, Matrix.permMatrixHom, Matrix.permMatrix_mulVec, Function.comp_def]

theorem cyclicResolvent_mulVec_constant {N : ℕ} [NeZero N]
    (profile : Fin N → Bool) (lam : ℂ) :
    (1 - lam • historyStep profile) *ᵥ (fun _ => (1 : ℂ)) =
      (1 - lam) • (fun _ => (1 : ℂ)) := by
  simp [Matrix.sub_mulVec, Matrix.smul_mulVec, sub_smul]

theorem cyclicInverse_mulVec_constant {N : ℕ} [NeZero N]
    (profile : Fin N → Bool) (lam : ℂ) (h1 : 1 - lam ≠ 0) (hN : 1 - lam ^ N ≠ 0) :
    cyclicInverse (historyStep profile) lam N *ᵥ (fun _ => (1 : ℂ)) =
      (1 - lam)⁻¹ • (fun _ => (1 : ℂ)) :=
  leftInverse_mulVec_eigen _ _ (cyclicInverse_mul _ _ _ (historyStep_pow_length profile) hN)
    _ _ h1 (cyclicResolvent_mulVec_constant profile lam)

theorem historyInverse_mulVec_constant {N : ℕ} [NeZero N]
    (profile : Fin N → Bool) (lam : ℂ) (h1 : 1 - lam ≠ 0) (hN : 1 - lam ^ N ≠ 0) :
    historyInverse profile lam *ᵥ (fun _ => (1 : ℂ)) =
      ((1 + lam) / (1 - lam)) • (fun _ => (1 : ℂ)) := by
  rw [historyInverse, Matrix.smul_mulVec, cyclicInverse_mulVec_constant profile lam h1 hN,
    smul_smul, div_eq_mul_inv]

/-- The actual history inverse attains the sharp `(1+lam)/(1-lam)` norm. -/
theorem historyInverse_norm {N : ℕ} [NeZero N] (profile : Fin N → Bool)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam < 1) :
    ‖historyInverse profile (lam : ℂ)‖ = (1 + lam) / (1 - lam) := by
  apply le_antisymm (historyInverse_norm_le profile lam h0 h1)
  have h1C : (1 : ℂ) - (lam : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (sub_pos.mpr h1))
  have hv : (fun _ : HistoryBasis N => (1 : ℂ)) ≠ 0 := by
    intro h
    have hh := congrFun h (0, false)
    norm_num at hh
  have hb := eigenvalue_norm_le_matrix_norm (historyInverse profile (lam : ℂ))
    (fun _ => (1 : ℂ)) hv _ (historyInverse_mulVec_constant profile (lam : ℂ) h1C
      (history_geometric_denominator_ne_zero lam h0 h1))
  have hr : 0 ≤ (1 + lam) / (1 - lam) := div_nonneg (by linarith) (by linarith)
  have hn : ‖((1 : ℂ) + (lam : ℂ)) / (1 - (lam : ℂ))‖ = (1 + lam) / (1 - lam) := by
    norm_cast
    exact Real.norm_of_nonneg hr
  rwa [hn] at hb

end OptimalQLS.LowerBounds
