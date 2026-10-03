import OptimalQLS.LowerBounds.HardFamilySignal

/-! Real entries, invertibility, and exact estimate promises of the hard family. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix

/-- Realness means the actual imaginary part of every matrix entry vanishes. -/
def EntrywiseReal {D E : Type*} (M : Matrix D E ℂ) : Prop := ∀ i j, (M i j).im = 0

theorem permutationMatrix_entrywiseReal {D : Type*} [DecidableEq D] (p : Equiv.Perm D) :
    EntrywiseReal (p.permMatrix ℂ) := by
  intro i j
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, apply_ite]

theorem historyStep_entrywiseReal {N : ℕ} [NeZero N] (profile : Fin N → Bool) :
    EntrywiseReal (historyStep profile) :=
  permutationMatrix_entrywiseReal _

theorem historyMatrix_entrywiseReal {N : ℕ} [NeZero N] (profile : Fin N → Bool) (lam : ℝ) :
    EntrywiseReal (historyMatrix profile (lam : ℂ)) := by
  intro i j
  have hb := historyStep_entrywiseReal profile i j
  have hn : ((1 : Matrix (HistoryBasis N) (HistoryBasis N) ℂ) i j -
      (lam : ℂ) * historyStep profile i j).im = 0 := by
    simp [Complex.sub_im, Complex.mul_im, hb, Matrix.one_apply, apply_ite]
  have hd : (((1 : ℂ) + (lam : ℂ))⁻¹).im = 0 := by simp [Complex.inv_im]
  change (((1 : ℂ) + (lam : ℂ))⁻¹ *
    ((1 : Matrix (HistoryBasis N) (HistoryBasis N) ℂ) i j - (lam : ℂ) * historyStep profile i j)).im = 0
  simp [Complex.mul_im, hn, hd]

theorem augmentedMatrix_entrywiseReal {D : Type*} [DecidableEq D]
    (H : Matrix D D ℂ) (hH : EntrywiseReal H) (kappa : ℝ) :
    EntrywiseReal (augmentedMatrix H kappa) := by
  intro i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [augmentedMatrix, Matrix.one_apply, Matrix.smul_apply, RCLike.real_smul_eq_coe_mul,
      Complex.mul_im, hH, apply_ite]
  all_goals exact hH _ _

theorem hermitianDilation_entrywiseReal {D : Type*} (G : Matrix D D ℂ) (hG : EntrywiseReal G) :
    EntrywiseReal (hermitianDilation G) := by
  intro i j
  cases i <;> cases j <;>
    simp [hermitianDilation, Matrix.conjTranspose_apply, hG]
  all_goals exact hG _ _

/-- Every hard-family matrix is literally real as well as Hermitian. -/
theorem hardFamilyMatrix_entrywiseReal {N m : ℕ} [NeZero N] (kappa : ℝ) (z : BitString m) :
    EntrywiseReal (hardFamilyMatrix N kappa z) :=
  hermitianDilation_entrywiseReal _ (augmentedMatrix_entrywiseReal _ (historyMatrix_entrywiseReal _ _) _)

theorem hardFamilyMatrix_isUnit {N m : ℕ} [NeZero N] {kappa : ℝ}
    (hk : 4 ≤ kappa) (z : BitString m) : IsUnit (hardFamilyMatrix N kappa z) := by
  have hp := hardFamily_augmented_inverse_pair (N := N) hk z
  have hleft : hardFamilyInverseCandidate N kappa z * hardFamilyMatrix N kappa z = 1 :=
    hermitianInverseCandidate_mul _ _ hp.1 hp.2
  have hright := mul_eq_one_comm.mp hleft
  exact ⟨⟨hardFamilyMatrix N kappa z, hardFamilyInverseCandidate N kappa z, hright, hleft⟩, rfl⟩

/-- The user-supplied estimate is genuinely a factor-two estimate of the exact
solution norm on every member of the single constructed family. -/
theorem hardFamily_solution_factor_two {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    ‖WithLp.toLp 2 ((hardFamilyMatrix N kappa z)⁻¹ *ᵥ hardFamilySource N m kappa estimate)‖ / 2 ≤ estimate ∧
      estimate ≤ 2 * ‖WithLp.toLp 2
        ((hardFamilyMatrix N kappa z)⁻¹ *ᵥ hardFamilySource N m kappa estimate)‖ := by
  rw [hardFamily_solution_norm hk he hek hN z]
  have hs := commonAdjustedScale_bounds hk he hek hN
  constructor <;> linarith [hs.1, hs.2.1]

end OptimalQLS.LowerBounds
