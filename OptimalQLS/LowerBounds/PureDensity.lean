import OptimalQLS.LowerBounds.SourceRotation
import OptimalQLS.LowerBounds.HardFamilySignal

/-! Literal rank-one density matrices and the existing history observable. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
variable {D : Type*} [Fintype D] [DecidableEq D]

def pureDensity (u : D → ℂ) : Matrix D D ℂ := ketBra u u

theorem pureDensity_positive (u : D → ℂ) : (pureDensity u).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star u

theorem pureDensity_trace (u : D → ℂ) : (pureDensity u).trace = (‖WithLp.toLp 2 u‖ ^ 2 : ℝ) := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 u)
  rw [pureDensity, ketBra, Matrix.trace_vecMulVec]
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, Complex.ofReal_pow] using h

theorem pureDensity_expectation (T : Matrix D D ℂ) (u : D → ℂ) :
    (T * pureDensity u).trace.re = pureExpectation T u := by
  rw [pureDensity, ketBra, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
  simp [pureExpectation, dotProduct, mul_comm]

theorem ketBra_self_norm_le_one (e : D → ℂ) (he : ‖WithLp.toLp 2 e‖ = 1) : ‖ketBra e e‖ ≤ 1 := by
  have hii : star e ⬝ᵥ e = 1 := by
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 e)
    simp only [EuclideanSpace.inner_eq_star_dotProduct, he, one_pow, Complex.ofReal_one] at h
    norm_num at h
    simpa only [dotProduct_comm] using h
  have hnorm := Matrix.l2_opNorm_conjTranspose_mul_self (ketBra e e)
  rw [ketBra_adjoint, ketBra_mul, hii, one_smul] at hnorm
  nlinarith [norm_nonneg (ketBra e e)]

theorem orthogonal_real_sum_norm_sq (y e : D → ℂ) (t : ℝ)
    (hye : inner ℂ (WithLp.toLp 2 y) (WithLp.toLp 2 e) = 0) (he : ‖WithLp.toLp 2 e‖ = 1) :
    ‖WithLp.toLp 2 (y + t • e)‖ ^ 2 = ‖WithLp.toLp 2 y‖ ^ 2 + t ^ 2 := by
  have hi : inner ℂ (WithLp.toLp 2 y) (t • WithLp.toLp 2 e) = 0 := by
    rw [inner_smul_right_eq_smul, hye, smul_zero]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (WithLp.toLp 2 y) (t • WithLp.toLp 2 e) hi
  rw [norm_smul, Real.norm_eq_abs, he, mul_one] at h
  change ‖WithLp.toLp 2 y + t • WithLp.toLp 2 e‖ ^ 2 = _
  nlinarith [sq_abs t]

/-- The history signal is about the literal pure-state density matrix. -/
theorem hardFamily_density_signal {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    (5 / 2304 : ℝ) * historyLambda kappa ^ (2 * m) ≤
      paritySign z * (hardFamilyObservable hk hN * pureDensity (normalizedHardFamilySolution N kappa estimate z)).trace.re := by
  rw [pureDensity_expectation]
  exact hardFamily_observable_signal hk he hek hN z

end OptimalQLS.LowerBounds
