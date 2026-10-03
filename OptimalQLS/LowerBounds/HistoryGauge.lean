import OptimalQLS.LowerBounds.HistoryTransition

/-!
# Gauge conjugacy and input-independent solution norm

These statements concern actual matrix-vector solutions and Euclidean norms.
The uniform padded source is fixed by the parity-history gauge, so all hidden
strings share one solution norm. The remaining quantitative lower bound on
that norm is a separate finite-amplitude estimate.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix

def gaugeMatrix {N : ℕ} (profile : Fin N → Bool) :
    Matrix (HistoryBasis N) (HistoryBasis N) ℂ :=
  Matrix.permMatrixHom (R := ℂ) (historyGauge profile)

@[simp] theorem historyGauge_zero {N : ℕ} :
    historyGauge (fun _ : Fin N => false) = 1 := by
  apply Equiv.ext
  rintro ⟨j, b⟩
  simp [historyGauge, gaugeMap]

theorem historyStep_intertwine {N : ℕ} [NeZero N] (profile : Fin N → Bool) :
    historyStep profile * gaugeMatrix profile =
      gaugeMatrix profile * historyStep (fun _ => false) := by
  unfold historyStep gaugeMatrix
  rw [← map_mul, ← map_mul]
  congr 1
  simp only [historyPermutation, historyGauge_zero, inv_one, one_mul, mul_one]
  group

theorem historyMatrix_intertwine {N : ℕ} [NeZero N] (profile : Fin N → Bool) (lam : ℂ) :
    historyMatrix profile lam * gaugeMatrix profile =
      gaugeMatrix profile * historyMatrix (fun _ => false) lam := by
  simp only [historyMatrix, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub,
    one_mul, mul_one]
  rw [historyStep_intertwine]

theorem historyInverse_intertwine {N : ℕ} [NeZero N] (profile : Fin N → Bool)
    (lam : ℂ) (hplus : 1 + lam ≠ 0) (hden : 1 - lam ^ N ≠ 0) :
    historyInverse profile lam * gaugeMatrix profile =
      gaugeMatrix profile * historyInverse (fun _ : Fin N => false) lam := by
  have hf := historyInverse_mul profile lam hplus hden
  have hzero := historyInverse_mul (fun _ : Fin N => false) lam hplus hden
  have hright := Matrix.mul_eq_one_comm.mp hzero
  calc
    historyInverse profile lam * gaugeMatrix profile =
        (historyInverse profile lam * gaugeMatrix profile) *
          (historyMatrix (fun _ => false) lam * historyInverse (fun _ : Fin N => false) lam) := by
      rw [hright, mul_one]
    _ = historyInverse profile lam *
        (gaugeMatrix profile * historyMatrix (fun _ => false) lam) *
          historyInverse (fun _ : Fin N => false) lam := by simp only [mul_assoc]
    _ = historyInverse profile lam * (historyMatrix profile lam * gaugeMatrix profile) *
          historyInverse (fun _ : Fin N => false) lam := by rw [← historyMatrix_intertwine]
    _ = (historyInverse profile lam * historyMatrix profile lam) * gaugeMatrix profile *
          historyInverse (fun _ : Fin N => false) lam := by simp only [mul_assoc]
    _ = gaugeMatrix profile * historyInverse (fun _ : Fin N => false) lam := by rw [hf, one_mul]

@[simp] theorem gaugeMatrix_mulVec {N : ℕ} (profile : Fin N → Bool)
    (v : HistoryBasis N → ℂ) (j : Fin N) (b : Bool) :
    (gaugeMatrix profile *ᵥ v) (j, b) = v (j, Bool.xor b (profile j)) := by
  simp [gaugeMatrix, Matrix.permMatrixHom, Matrix.permMatrix_mulVec, historyGauge, gaugeMap,
    Function.comp_def]

/-- The gauge preserves the genuine Euclidean norm of every vector. -/
theorem norm_gaugeMatrix_mulVec {N : ℕ} (profile : Fin N → Bool)
    (v : HistoryBasis N → ℂ) :
    ‖WithLp.toLp 2 (gaugeMatrix profile *ᵥ v)‖ = ‖WithLp.toLp 2 v‖ := by
  simp only [gaugeMatrix, Matrix.permMatrixHom_apply, Matrix.permMatrix_mulVec,
    EuclideanSpace.norm_eq]
  change Real.sqrt (∑ b, ‖v ((historyGauge profile)⁻¹ b)‖ ^ 2) =
    Real.sqrt (∑ b, ‖v b‖ ^ 2)
  congr 1
  exact Equiv.sum_comp ((historyGauge profile)⁻¹) (fun b => ‖v b‖ ^ 2)

/-- Actual padded source, constant on the first ell clock values and work 0. -/
def uniformHistorySource {N : ℕ} (ell : ℕ) : HistoryBasis N → ℂ :=
  fun b => if b.1.val < ell ∧ b.2 = false then ((Real.sqrt (ell : ℝ))⁻¹ : ℂ) else 0

theorem gaugeMatrix_uniformHistorySource {N ell : ℕ} (profile : Fin N → Bool)
    (hfixed : ∀ j : Fin N, j.val < ell → profile j = false) :
    gaugeMatrix profile *ᵥ uniformHistorySource ell = uniformHistorySource ell := by
  funext b
  rcases b with ⟨j, b⟩
  rw [gaugeMatrix_mulVec]
  by_cases hj : j.val < ell
  · simp [uniformHistorySource, hfixed j hj]
  · simp [uniformHistorySource, hj]

/-- Exact gauge relation between the full solution vectors. -/
theorem history_solution_gauge {N ell : ℕ} [NeZero N] (profile : Fin N → Bool)
    (hfixed : ∀ j : Fin N, j.val < ell → profile j = false)
    (lam : ℂ) (hplus : 1 + lam ≠ 0) (hden : 1 - lam ^ N ≠ 0) :
    historyInverse profile lam *ᵥ uniformHistorySource ell =
      gaugeMatrix profile *ᵥ (historyInverse (fun _ : Fin N => false) lam *ᵥ uniformHistorySource ell) := by
  rw [Matrix.mulVec_mulVec, ← historyInverse_intertwine profile lam hplus hden,
    ← Matrix.mulVec_mulVec, gaugeMatrix_uniformHistorySource profile hfixed]

/-- The solution norm is independent of the computation on every source-fixed
clock gauge; applies directly to every padded parity input. -/
theorem history_solution_norm_independent {N ell : ℕ} [NeZero N] (profile : Fin N → Bool)
    (hfixed : ∀ j : Fin N, j.val < ell → profile j = false)
    (lam : ℂ) (hplus : 1 + lam ≠ 0) (hden : 1 - lam ^ N ≠ 0) :
    ‖WithLp.toLp 2 (historyInverse profile lam *ᵥ uniformHistorySource ell)‖ =
      ‖WithLp.toLp 2 (historyInverse (fun _ : Fin N => false) lam *ᵥ uniformHistorySource ell)‖ := by
  rw [history_solution_gauge profile hfixed lam hplus hden, norm_gaugeMatrix_mulVec]

/-- Definition 6.2's actual parity gauge meets the source-fixed premise. -/
theorem parityHistoryProfile_source_fixed (ell : ℕ) (z : List Bool)
    (j : Fin (parityHistoryGates ell z).length) (hj : j.val < ell) :
    parityHistoryProfile ell z j = false :=
  parityHistoryGates_initial_prefix z hj

end OptimalQLS.LowerBounds
