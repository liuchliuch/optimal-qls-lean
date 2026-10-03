import OptimalQLS.LowerBounds.AugmentedHistory

/-! The fixed unit least-eigenvalue direction and exact orthogonality in6.4. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
variable {D : Type*} [Fintype D] [DecidableEq D]

theorem augmentedMatrix_conjTranspose (H : Matrix D D ℂ) (kappa : ℝ) :
    (augmentedMatrix H kappa).conjTranspose = augmentedMatrix H.conjTranspose kappa := by
  simp [augmentedMatrix, Matrix.fromBlocks_conjTranspose]

theorem augmentedLastDirection_adjoint_eigen (H : Matrix D D ℂ) (kappa : ℝ) :
    (augmentedMatrix H kappa).conjTranspose *ᵥ augmentedLastDirection =
      kappa⁻¹ • augmentedLastDirection := by
  rw [augmentedMatrix_conjTranspose]
  exact augmentedLastDirection_eigen _ _

theorem sumElim_inner {E : Type*} [Fintype E] (u u' : D → ℂ) (v v' : E → ℂ) :
    inner ℂ (WithLp.toLp 2 (Sum.elim u v)) (WithLp.toLp 2 (Sum.elim u' v')) =
      inner ℂ (WithLp.toLp 2 u) (WithLp.toLp 2 u') + inner ℂ (WithLp.toLp 2 v) (WithLp.toLp 2 v') := by
  simp [PiLp.inner_apply, Fintype.sum_sum_type]

theorem augmentedVector_inner_last (a beta : ℝ) (b : D → ℂ) :
    inner ℂ (WithLp.toLp 2 (augmentedVector a beta b))
      (WithLp.toLp 2 (augmentedLastDirection (D := D))) = 0 := by
  simp [augmentedVector, augmentedLastDirection, PiLp.inner_apply, Fintype.sum_sum_type]

/-- The symmetric unit direction supported on the two final scalar blocks. -/
def dilatedLastDirection : (AugmentedIndex D ⊕ AugmentedIndex D) → ℂ :=
  (Real.sqrt 2)⁻¹ • Sum.elim augmentedLastDirection augmentedLastDirection

theorem dilatedLastDirection_norm : ‖WithLp.toLp 2 (dilatedLastDirection (D := D))‖ = 1 := by
  have hsq : ‖WithLp.toLp 2 (dilatedLastDirection (D := D))‖ ^ 2 = 1 := by
    change ‖(Real.sqrt 2)⁻¹ • WithLp.toLp 2
      (Sum.elim (augmentedLastDirection (D := D)) augmentedLastDirection)‖ ^ 2 = 1
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, sumElim_norm_sq,
      augmentedLastDirection_norm]
    norm_num
  nlinarith [norm_nonneg (WithLp.toLp 2 (dilatedLastDirection (D := D)))]

theorem dilatedLastDirection_eigen (H : Matrix D D ℂ) (kappa : ℝ) :
    hermitianDilation (augmentedMatrix H kappa) *ᵥ dilatedLastDirection =
      kappa⁻¹ • dilatedLastDirection := by
  have hG : augmentedMatrix H kappa *ᵥ augmentedLastDirection =
      (kappa⁻¹ : ℂ) • augmentedLastDirection := by
    rw [augmentedLastDirection_eigen]
    funext i
    simp [Pi.smul_apply, RCLike.real_smul_eq_coe_mul, Complex.ofReal_inv]
  have hGt : (augmentedMatrix H kappa).conjTranspose *ᵥ augmentedLastDirection =
      (kappa⁻¹ : ℂ) • augmentedLastDirection := by
    rw [augmentedLastDirection_adjoint_eigen]
    funext i
    simp [Pi.smul_apply, RCLike.real_smul_eq_coe_mul, Complex.ofReal_inv]
  rw [dilatedLastDirection, Matrix.mulVec_smul, hermitianDilation_eigen _ _ _ hG hGt]
  funext i
  simp [Pi.smul_apply, RCLike.real_smul_eq_coe_mul, mul_comm, mul_left_comm, mul_assoc]

/-- The direction is orthogonal to every augmented source in the first half. -/
theorem dilatedLastDirection_orthogonal_left (a beta : ℝ) (b : D → ℂ) :
    inner ℂ (WithLp.toLp 2 (Sum.elim (augmentedVector a beta b) (0 : AugmentedIndex D → ℂ)))
      (WithLp.toLp 2 (dilatedLastDirection (D := D))) = 0 := by
  change inner ℂ (WithLp.toLp 2 (Sum.elim (augmentedVector a beta b) (0 : AugmentedIndex D → ℂ)))
    ((Real.sqrt 2)⁻¹ • WithLp.toLp 2 (Sum.elim augmentedLastDirection augmentedLastDirection)) = 0
  rw [inner_smul_right_eq_smul, sumElim_inner, augmentedVector_inner_last]
  simp

/-- The direction is also orthogonal to every corresponding inverse solution
in the second half, regardless of the history output vector. -/
theorem dilatedLastDirection_orthogonal_right (a beta : ℝ) (b : D → ℂ) :
    inner ℂ (WithLp.toLp 2 (Sum.elim (0 : AugmentedIndex D → ℂ) (augmentedVector a beta b)))
      (WithLp.toLp 2 (dilatedLastDirection (D := D))) = 0 := by
  change inner ℂ (WithLp.toLp 2 (Sum.elim (0 : AugmentedIndex D → ℂ) (augmentedVector a beta b)))
    ((Real.sqrt 2)⁻¹ • WithLp.toLp 2 (Sum.elim augmentedLastDirection augmentedLastDirection)) = 0
  rw [inner_smul_right_eq_smul, sumElim_inner, augmentedVector_inner_last]
  simp

end OptimalQLS.LowerBounds
