import OptimalQLS.LowerBounds.AugmentedHistory

/-! Exact observable transport through the source mixture and Hermitian embedding. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
variable {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

theorem pureExpectation_blockDiagonal (A : Matrix D D ℂ) (B : Matrix E E ℂ)
    (u : D → ℂ) (v : E → ℂ) :
    pureExpectation (Matrix.fromBlocks A 0 0 B) (Sum.elim u v) =
      pureExpectation A u + pureExpectation B v := by
  unfold pureExpectation
  rw [Matrix.fromBlocks_mulVec]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec,
    add_zero, zero_add, Fintype.sum_sum_type, Complex.add_re]

@[simp] theorem pureExpectation_zero_matrix (v : D → ℂ) : pureExpectation (0 : Matrix D D ℂ) v = 0 := by
  simp [pureExpectation]

@[simp] theorem pureExpectation_zero_vector (M : Matrix D D ℂ) : pureExpectation M (0 : D → ℂ) = 0 := by
  simp [pureExpectation]

/-- Actual quadratic expectations scale by the square of a real amplitude. -/
theorem pureExpectation_real_smul (M : Matrix D D ℂ) (v : D → ℂ) (c : ℝ) :
    pureExpectation M (c • v) = c ^ 2 * pureExpectation M v := by
  unfold pureExpectation
  rw [Matrix.mulVec_smul]
  have heq : (∑ i, star ((c • v) i) * (c • (M *ᵥ v)) i) =
      (c ^ 2 : ℝ) * (∑ i, star (v i) * (M *ᵥ v) i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [Pi.smul_apply, RCLike.real_smul_eq_coe_mul, StarMul.star_mul, mul_comm, mul_left_comm,
      mul_assoc, pow_two]
  rw [heq]
  simp [pow_two]

def augmentedObservable (M : Matrix D D ℂ) : Matrix (AugmentedIndex D) (AugmentedIndex D) ℂ :=
  Matrix.fromBlocks 0 0 0 (Matrix.fromBlocks M 0 0 (0 : Matrix Unit Unit ℂ))

def dilatedObservable (M : Matrix D D ℂ) :
    Matrix (AugmentedIndex D ⊕ AugmentedIndex D) (AugmentedIndex D ⊕ AugmentedIndex D) ℂ :=
  Matrix.fromBlocks 0 0 0 (augmentedObservable M)

theorem augmentedObservable_hermitian (M : Matrix D D ℂ) (hM : M.IsHermitian) :
    (augmentedObservable M).IsHermitian := by
  simp [augmentedObservable, Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose]
  exact hM

theorem dilatedObservable_hermitian (M : Matrix D D ℂ) (hM : M.IsHermitian) :
    (dilatedObservable M).IsHermitian := by
  have h := augmentedObservable_hermitian M hM
  simp [dilatedObservable, Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose]
  exact h

theorem augmentedObservable_norm (M : Matrix D D ℂ) : ‖augmentedObservable M‖ = ‖M‖ := by
  simp [augmentedObservable, blockDiagonal_norm, max_eq_left (norm_nonneg M), max_eq_right (norm_nonneg M)]

theorem dilatedObservable_norm (M : Matrix D D ℂ) : ‖dilatedObservable M‖ = ‖M‖ := by
  simp [dilatedObservable, blockDiagonal_norm, augmentedObservable_norm, max_eq_right (norm_nonneg M)]

theorem augmentedObservable_expectation (M : Matrix D D ℂ) (a beta : ℝ) (v : D → ℂ) :
    pureExpectation (augmentedObservable M) (augmentedVector a beta v) =
      beta ^ 2 * pureExpectation M v := by
  rw [augmentedObservable, augmentedVector, pureExpectation_blockDiagonal, pureExpectation_blockDiagonal]
  simp [pureExpectation_real_smul]

/-- Exact fraction of the normalized full solution's expectation arising from
the history subsystem; the scalar weight is later bounded below by5/9. -/
theorem dilatedObservable_normalized_expectation (M : Matrix D D ℂ) (a beta s Y : ℝ)
    (v : D → ℂ) (hY : Y ≠ 0) :
    pureExpectation (dilatedObservable M)
      (s⁻¹ • Sum.elim (0 : AugmentedIndex D → ℂ) (augmentedVector a beta v)) =
      (beta ^ 2 * Y ^ 2 / s ^ 2) * pureExpectation M (Y⁻¹ • v) := by
  rw [pureExpectation_real_smul, dilatedObservable, pureExpectation_blockDiagonal]
  simp only [pureExpectation_zero_vector, zero_add, augmentedObservable_expectation,
    pureExpectation_real_smul, inv_pow]
  field_simp

end OptimalQLS.LowerBounds
