import OptimalQLS.LowerBounds.NormAdjustmentScalars
import OptimalQLS.LowerBounds.StatePreparation

/-!
# Actual direct-sum matrix and source for the norm-controlled hard family

The first scalar block adjusts the solution norm; the last scalar block
provides the fixed least-eigenvalue direction. Their matrices and source
coordinates are explicit. The middle block remains the actual history matrix.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
variable {D : Type*} [Fintype D] [DecidableEq D]

abbrev AugmentedIndex (D : Type*) := Unit ⊕ (D ⊕ Unit)

def augmentedMatrix (H : Matrix D D ℂ) (kappa : ℝ) :
    Matrix (AugmentedIndex D) (AugmentedIndex D) ℂ :=
  Matrix.fromBlocks 1 0 0 (Matrix.fromBlocks H 0 0 (kappa⁻¹ • (1 : Matrix Unit Unit ℂ)))

def augmentedInverse (T : Matrix D D ℂ) (kappa : ℝ) :
    Matrix (AugmentedIndex D) (AugmentedIndex D) ℂ :=
  Matrix.fromBlocks 1 0 0 (Matrix.fromBlocks T 0 0 (kappa • (1 : Matrix Unit Unit ℂ)))

theorem augmentedInverse_mul (H T : Matrix D D ℂ) (kappa : ℝ) (hk : kappa ≠ 0) (hTH : T * H = 1) :
    augmentedInverse T kappa * augmentedMatrix H kappa = 1 := by
  rw [augmentedInverse, augmentedMatrix, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, Matrix.one_mul]
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, mul_smul_comm,
    Matrix.mul_one, smul_smul, hTH, inv_mul_cancel₀ hk, one_smul, Matrix.fromBlocks_one]

theorem augmentedMatrix_mul_inverse (H T : Matrix D D ℂ) (kappa : ℝ) (hk : kappa ≠ 0) (hHT : H * T = 1) :
    augmentedMatrix H kappa * augmentedInverse T kappa = 1 := by
  rw [augmentedInverse, augmentedMatrix, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, Matrix.one_mul]
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, mul_smul_comm,
    Matrix.mul_one, smul_smul, hHT, mul_inv_cancel₀ hk, one_smul, Matrix.fromBlocks_one]

theorem augmentedMatrix_norm {kappa : ℝ} (hk : 1 ≤ kappa) (H : Matrix D D ℂ) (hH : ‖H‖ = 1) :
    ‖augmentedMatrix H kappa‖ = 1 := by
  have hp : 0 < kappa := by linarith
  have hi : kappa⁻¹ ≤ 1 := (inv_le_one₀ hp).mpr hk
  simp only [augmentedMatrix, blockDiagonal_norm, norm_one, hH, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hp.le), mul_one, max_self]
  rw [max_eq_left hi, max_self]

theorem augmentedInverse_norm {kappa : ℝ} (hk : 1 ≤ kappa) (T : Matrix D D ℂ) (hT : ‖T‖ = kappa) :
    ‖augmentedInverse T kappa‖ = kappa := by
  have hp : 0 ≤ kappa := by linarith
  simp [augmentedInverse, blockDiagonal_norm, hT, norm_smul, Real.norm_eq_abs, abs_of_nonneg hp,
    max_eq_right hk]

/-- Source coordinates, with an exactly zero last scalar component. -/
def augmentedVector (a beta : ℝ) (b : D → ℂ) : AugmentedIndex D → ℂ :=
  Sum.elim (fun _ : Unit => (a : ℂ)) (Sum.elim (beta • b) (0 : Unit → ℂ))

@[simp] theorem unitCoordinate_norm (a : ℂ) : ‖WithLp.toLp 2 (fun _ : Unit => a)‖ = ‖a‖ := by
  simp [EuclideanSpace.norm_eq]

theorem augmentedVector_norm_sq (a beta : ℝ) (b : D → ℂ) :
    ‖WithLp.toLp 2 (augmentedVector a beta b)‖ ^ 2 = a ^ 2 + beta ^ 2 * ‖WithLp.toLp 2 b‖ ^ 2 := by
  rw [augmentedVector, sumElim_norm_sq, sumElim_norm_left, unitCoordinate_norm]
  have hbeta : ‖WithLp.toLp 2 (beta • b)‖ = |beta| * ‖WithLp.toLp 2 b‖ := by
    change ‖beta • WithLp.toLp 2 b‖ = _
    simp only [norm_smul, Real.norm_eq_abs]
  rw [hbeta, mul_pow]
  simp [Complex.norm_real, sq_abs]

theorem augmentedInverse_source (T : Matrix D D ℂ) (kappa a beta : ℝ) (b : D → ℂ) :
    augmentedInverse T kappa *ᵥ augmentedVector a beta b = augmentedVector a beta (T *ᵥ b) := by
  rw [augmentedInverse, augmentedVector, Matrix.fromBlocks_mulVec]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, Matrix.one_mulVec,
    Matrix.zero_mulVec, add_zero, zero_add]
  rw [Matrix.fromBlocks_mulVec]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec,
    add_zero, zero_add, Matrix.mulVec_smul, smul_zero]
  change Sum.elim (fun _ : Unit => (a : ℂ))
      (Sum.elim (beta • (T *ᵥ b)) ((kappa • (1 : Matrix Unit Unit ℂ)) *ᵥ (0 : Unit → ℂ))) = _
  rw [Matrix.mulVec_zero]
  rfl

def adjustedSource (b : D → ℂ) (Y s : ℝ) : AugmentedIndex D → ℂ :=
  augmentedVector (identitySourceCoefficient Y s) (historySourceCoefficient Y s) b

theorem adjustedSource_norm {Y s : ℝ} (hs : 3 / 2 ≤ s) (hsY : s ≤ Y)
    (b : D → ℂ) (hb : ‖WithLp.toLp 2 b‖ = 1) :
    ‖WithLp.toLp 2 (adjustedSource b Y s)‖ = 1 := by
  have hsq : ‖WithLp.toLp 2 (adjustedSource b Y s)‖ ^ 2 = 1 := by
    rw [adjustedSource, augmentedVector_norm_sq, hb]
    simpa using adjustment_source_identity hs hsY
  nlinarith [norm_nonneg (WithLp.toLp 2 (adjustedSource b Y s))]

theorem adjustedSource_inverse_norm {Y s : ℝ} (hs : 3 / 2 ≤ s) (hsY : s ≤ Y)
    (T : Matrix D D ℂ) (kappa : ℝ) (b : D → ℂ) (hY : ‖WithLp.toLp 2 (T *ᵥ b)‖ = Y) :
    ‖WithLp.toLp 2 (augmentedInverse T kappa *ᵥ adjustedSource b Y s)‖ = s := by
  rw [adjustedSource, augmentedInverse_source]
  have hsq : ‖WithLp.toLp 2 (augmentedVector (identitySourceCoefficient Y s)
      (historySourceCoefficient Y s) (T *ᵥ b))‖ ^ 2 = s ^ 2 := by
    rw [augmentedVector_norm_sq, hY]
    simpa [mul_comm] using adjustment_solution_identity hs hsY
  nlinarith [norm_nonneg (WithLp.toLp 2 (augmentedVector (identitySourceCoefficient Y s)
    (historySourceCoefficient Y s) (T *ᵥ b)))]

/-- The final scalar basis direction, independent of H and of the source norm. -/
def augmentedLastDirection : AugmentedIndex D → ℂ :=
  Sum.elim (0 : Unit → ℂ) (Sum.elim (0 : D → ℂ) (fun _ : Unit => 1))

theorem augmentedLastDirection_norm : ‖WithLp.toLp 2 (augmentedLastDirection (D := D))‖ = 1 := by
  simp [augmentedLastDirection]

theorem augmentedLastDirection_eigen (H : Matrix D D ℂ) (kappa : ℝ) :
    augmentedMatrix H kappa *ᵥ augmentedLastDirection = kappa⁻¹ • augmentedLastDirection := by
  rw [augmentedMatrix, augmentedLastDirection, Matrix.fromBlocks_mulVec]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec,
    Matrix.one_mulVec, add_zero, zero_add]
  rw [Matrix.fromBlocks_mulVec]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, add_zero, zero_add]
  funext i
  cases i with
  | inl i => simp
  | inr i =>
    cases i with
    | inl i =>
      simp only [Sum.elim_inr, Sum.elim_inl, Pi.smul_apply, Pi.zero_apply, smul_zero]
      change (H *ᵥ (0 : D → ℂ)) i = 0
      rw [Matrix.mulVec_zero]
      rfl
    | inr i => simp

end OptimalQLS.LowerBounds
