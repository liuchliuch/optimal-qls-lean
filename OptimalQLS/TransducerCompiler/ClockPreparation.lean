import OptimalQLS.OracleCircuit
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Tactic

/-!
# Exact real clock preparation

An explicit real orthogonal reflection prepares the uniform clock vector.
This proves exact matrix semantics, not a logarithmic-size gate synthesis.
-/

noncomputable section
namespace OptimalQLS.TransducerCompiler
open Matrix
open scoped RealInnerProductSpace

/-- The normalized uniform real clock state. -/
def uniformClockReal (K : ℕ) : EuclideanSpace ℝ (Fin K) :=
  WithLp.toLp 2 (fun _ => (Real.sqrt (K : ℝ))⁻¹)

theorem uniformClockReal_norm {K : ℕ} (hK : 0 < K) :
    ‖uniformClockReal K‖ = 1 := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hs : 0 < Real.sqrt (K : ℝ) := Real.sqrt_pos.2 hKr
  have heq : ‖uniformClockReal K‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [uniformClockReal, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [inv_pow, Real.sq_sqrt hKr.le, mul_inv_cancel₀ (ne_of_gt hKr)]
  nlinarith [norm_nonneg (uniformClockReal K)]

/-- Reflect about the bisecting hyperplane of the basis state and uniform state. -/
def clockPrepareIsometry {K : ℕ} (zero : Fin K) :
    EuclideanSpace ℝ (Fin K) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin K) :=
  Submodule.reflection
    (ℝ ∙ ((EuclideanSpace.basisFun (Fin K) ℝ) zero - uniformClockReal K))ᗮ

theorem clockPrepareIsometry_basis {K : ℕ} (zero : Fin K) :
    clockPrepareIsometry zero ((EuclideanSpace.basisFun (Fin K) ℝ) zero) =
      uniformClockReal K := by
  apply Submodule.reflection_sub
  rw [OrthonormalBasis.norm_eq_one, uniformClockReal_norm (Nat.zero_lt_of_lt zero.isLt)]

/-- Matrix of the real clock-preparation reflection in the computational basis. -/
def clockPrepareReal {K : ℕ} (zero : Fin K) : Matrix.unitaryGroup (Fin K) ℝ :=
  ⟨(EuclideanSpace.basisFun (Fin K) ℝ).toBasis.toMatrix
      ((EuclideanSpace.basisFun (Fin K) ℝ).map (clockPrepareIsometry zero)),
    (EuclideanSpace.basisFun (Fin K) ℝ).toMatrix_orthonormalBasis_mem_unitary _⟩

theorem clockPrepareReal_apply {K : ℕ} (zero : Fin K) (i j : Fin K) :
    (clockPrepareReal zero : Matrix (Fin K) (Fin K) ℝ) i j =
      clockPrepareIsometry zero ((EuclideanSpace.basisFun (Fin K) ℝ) j) i := by
  simp [clockPrepareReal, Module.Basis.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply]

/-- The reflection sends the selected computational basis state to uniform amplitude. -/
theorem clockPrepareReal_mulVec_single {K : ℕ} (zero : Fin K) :
    (clockPrepareReal zero : Matrix (Fin K) (Fin K) ℝ) *ᵥ Pi.single zero 1 =
      fun _ => (Real.sqrt (K : ℝ))⁻¹ := by
  ext i
  simp only [Matrix.mulVec_single, MulOpposite.op_one, one_smul]
  change (clockPrepareReal zero : Matrix (Fin K) (Fin K) ℝ) i zero = _
  rw [clockPrepareReal_apply]
  rw [clockPrepareIsometry_basis]
  rfl

/-- Entrywise complexification preserves unitarity of a real orthogonal matrix. -/
def complexifyRealUnitary {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℝ) : Matrix.unitaryGroup n ℂ := by
  refine ⟨(U : Matrix n n ℝ).map Complex.ofReal, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff]
  have hU := (Matrix.mem_unitaryGroup_iff.mp U.property)
  ext i j
  have hij := congr_fun (congr_fun hU i) j
  simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, star_trivial] at hij
  simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Matrix.map_apply, Complex.star_def,
    Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  rw [hij]
  simp only [Matrix.one_apply]
  split_ifs <;> simp

/-- Actual complex unitary matrix for the real preparation operation. -/
def clockPrepare {K : ℕ} (zero : Fin K) : Matrix.unitaryGroup (Fin K) ℂ :=
  complexifyRealUnitary (clockPrepareReal zero)

theorem clockPrepare_real {K : ℕ} (zero : Fin K) (i j : Fin K) :
    ((clockPrepare zero : Matrix (Fin K) (Fin K) ℂ) i j).im = 0 := rfl

theorem clockPrepare_mulVec_single {K : ℕ} (zero : Fin K) :
    (clockPrepare zero : Matrix (Fin K) (Fin K) ℂ) *ᵥ Pi.single zero 1 =
      fun _ => ((Real.sqrt (K : ℝ))⁻¹ : ℂ) := by
  ext i
  simp only [Matrix.mulVec_single, MulOpposite.op_one, one_smul]
  change ((clockPrepareReal zero : Matrix (Fin K) (Fin K) ℝ) i zero : ℂ) = _
  rw [clockPrepareReal_apply, clockPrepareIsometry_basis]
  simp [uniformClockReal]

/-- Applying the adjoint restores the selected computational basis clock state. -/
theorem clockPrepare_adjoint_mulVec_uniform {K : ℕ} (zero : Fin K) :
    star (clockPrepare zero : Matrix (Fin K) (Fin K) ℂ) *ᵥ
        (fun _ => ((Real.sqrt (K : ℝ))⁻¹ : ℂ)) = Pi.single zero 1 := by
  rw [← clockPrepare_mulVec_single zero, Matrix.mulVec_mulVec,
    (clockPrepare zero).property.1, Matrix.one_mulVec]

end OptimalQLS.TransducerCompiler
