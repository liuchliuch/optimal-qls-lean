import OptimalQLS.LowerBounds.HistoryObservable

/-! Euclidean operator norms of concrete direct-sum matrices. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix

variable {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

theorem sumElim_norm_sq (u : D → ℂ) (v : E → ℂ) :
    ‖WithLp.toLp 2 (Sum.elim u v)‖ ^ 2 = ‖WithLp.toLp 2 u‖ ^ 2 + ‖WithLp.toLp 2 v‖ ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]

@[simp] theorem sumElim_norm_left (u : D → ℂ) :
    ‖WithLp.toLp 2 (Sum.elim u (0 : E → ℂ))‖ = ‖WithLp.toLp 2 u‖ := by
  have h := sumElim_norm_sq u (0 : E → ℂ)
  simp only [WithLp.toLp_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at h
  nlinarith [norm_nonneg (WithLp.toLp 2 (Sum.elim u (0 : E → ℂ))), norm_nonneg (WithLp.toLp 2 u)]

@[simp] theorem sumElim_norm_right (v : E → ℂ) :
    ‖WithLp.toLp 2 (Sum.elim (0 : D → ℂ) v)‖ = ‖WithLp.toLp 2 v‖ := by
  have h := sumElim_norm_sq (0 : D → ℂ) v
  simp only [WithLp.toLp_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at h
  nlinarith [norm_nonneg (WithLp.toLp 2 (Sum.elim (0 : D → ℂ) v)), norm_nonneg (WithLp.toLp 2 v)]

/-- Upper direct-sum norm estimate, proved by squared Euclidean coordinates. -/
theorem blockDiagonal_norm_le (A : Matrix D D ℂ) (B : Matrix E E ℂ) :
    ‖Matrix.fromBlocks A 0 0 B‖ ≤ max ‖A‖ ‖B‖ := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  have hc : 0 ≤ max ‖A‖ ‖B‖ := le_trans (norm_nonneg A) (le_max_left _ _)
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro x
  let u : D → ℂ := fun i => x (Sum.inl i)
  let v : E → ℂ := fun i => x (Sum.inr i)
  have hA := A.l2_opNorm_mulVec (WithLp.toLp 2 u)
  have hB := B.l2_opNorm_mulVec (WithLp.toLp 2 v)
  change ‖WithLp.toLp 2 (A *ᵥ u)‖ ≤ ‖A‖ * ‖WithLp.toLp 2 u‖ at hA
  change ‖WithLp.toLp 2 (B *ᵥ v)‖ ≤ ‖B‖ * ‖WithLp.toLp 2 v‖ at hB
  have hAu := hA.trans (mul_le_mul_of_nonneg_right (le_max_left ‖A‖ ‖B‖) (norm_nonneg _))
  have hBv := hB.trans (mul_le_mul_of_nonneg_right (le_max_right ‖A‖ ‖B‖) (norm_nonneg _))
  have hAsq := pow_le_pow_left₀ (norm_nonneg (WithLp.toLp 2 (A *ᵥ u))) hAu 2
  have hBsq := pow_le_pow_left₀ (norm_nonneg (WithLp.toLp 2 (B *ᵥ v))) hBv 2
  have hx : ‖x‖ ^ 2 = ‖WithLp.toLp 2 u‖ ^ 2 + ‖WithLp.toLp 2 v‖ ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, u, v]
  change ‖WithLp.toLp 2 ((Matrix.fromBlocks A 0 0 B) *ᵥ (fun i => x i))‖ ≤ _
  rw [Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, add_zero, zero_add]
  change ‖WithLp.toLp 2 (Sum.elim (A *ᵥ u) (B *ᵥ v))‖ ≤ max ‖A‖ ‖B‖ * ‖x‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg x))).mp
  rw [sumElim_norm_sq, mul_pow, hx]
  nlinarith

theorem left_norm_le_blockDiagonal (A : Matrix D D ℂ) (B : Matrix E E ℂ) :
    ‖A‖ ≤ ‖Matrix.fromBlocks A 0 0 B‖ := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM A]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have h := (Matrix.fromBlocks A 0 0 B).l2_opNorm_mulVec
    (WithLp.toLp 2 (Sum.elim (fun i => x i) (0 : E → ℂ)))
  change ‖WithLp.toLp 2 ((Matrix.fromBlocks A 0 0 B) *ᵥ
      Sum.elim (fun i => x i) (0 : E → ℂ))‖ ≤ _ at h
  rw [Matrix.fromBlocks_mulVec] at h
  simpa only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec,
    Matrix.mulVec_zero, add_zero, zero_add, sumElim_norm_left] using h

theorem right_norm_le_blockDiagonal (A : Matrix D D ℂ) (B : Matrix E E ℂ) :
    ‖B‖ ≤ ‖Matrix.fromBlocks A 0 0 B‖ := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM B]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have h := (Matrix.fromBlocks A 0 0 B).l2_opNorm_mulVec
    (WithLp.toLp 2 (Sum.elim (0 : D → ℂ) (fun i => x i)))
  change ‖WithLp.toLp 2 ((Matrix.fromBlocks A 0 0 B) *ᵥ
      Sum.elim (0 : D → ℂ) (fun i => x i))‖ ≤ _ at h
  rw [Matrix.fromBlocks_mulVec] at h
  simpa only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec,
    Matrix.mulVec_zero, add_zero, zero_add, sumElim_norm_right] using h

/-- Exact L2 operator norm of a block diagonal sum. -/
theorem blockDiagonal_norm (A : Matrix D D ℂ) (B : Matrix E E ℂ) :
    ‖Matrix.fromBlocks A 0 0 B‖ = max ‖A‖ ‖B‖ :=
  le_antisymm (blockDiagonal_norm_le A B)
    (max_le (left_norm_le_blockDiagonal A B) (right_norm_le_blockDiagonal A B))

end OptimalQLS.LowerBounds
