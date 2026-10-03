import OptimalQLS.LowerBounds.QueryPortDistance
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# An explicit full oracle rotation in an orthogonal source plane

Every matrix entry is fixed by the two source vectors. No choice of unknown
columns or preparation-oracle extension is used in the perturbation.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
variable {D : Type*} [Fintype D] [DecidableEq D]

def ketBra (u v : D → ℂ) : Matrix D D ℂ := Matrix.vecMulVec u (star v)

@[simp] theorem ketBra_adjoint (u v : D → ℂ) : (ketBra u v).conjTranspose = ketBra v u := by
  ext i j
  simp [ketBra, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, mul_comm]

theorem ketBra_mul (u v w x : D → ℂ) :
    ketBra u v * ketBra w x = (star v ⬝ᵥ w) • ketBra u x := by
  rw [ketBra, ketBra, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]
  rfl

theorem ketBra_mulVec (u v w : D → ℂ) : ketBra u v *ᵥ w = (star v ⬝ᵥ w) • u := by
  ext i
  simp [ketBra, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

def sourcePlaneProjection (b e : D → ℂ) : Matrix D D ℂ := ketBra b b + ketBra e e

def sourcePlaneGenerator (b e : D → ℂ) : Matrix D D ℂ := ketBra e b - ketBra b e

structure OrthogonalUnitPair (b e : D → ℂ) : Prop where
  source_unit : star b ⬝ᵥ b = 1
  direction_unit : star e ⬝ᵥ e = 1
  source_direction : star b ⬝ᵥ e = 0
  direction_source : star e ⬝ᵥ b = 0

theorem orthogonalUnitPair_of_norm_inner (b e : D → ℂ)
    (hb : ‖WithLp.toLp 2 b‖ = 1) (he : ‖WithLp.toLp 2 e‖ = 1)
    (hbe : inner ℂ (WithLp.toLp 2 b) (WithLp.toLp 2 e) = 0) : OrthogonalUnitPair b e := by
  have hbb := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 b)
  have hee := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 e)
  have heb : inner ℂ (WithLp.toLp 2 e) (WithLp.toLp 2 b) = 0 := by
    rw [← inner_conj_symm, hbe]
    simp
  simp only [EuclideanSpace.inner_eq_star_dotProduct] at hbb hee hbe heb
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [hb, dotProduct_comm] using hbb
  · simpa [he, dotProduct_comm] using hee
  · simpa [dotProduct_comm] using hbe
  · simpa [dotProduct_comm] using heb

theorem sourcePlane_algebra (b e : D → ℂ) (h : OrthogonalUnitPair b e) :
    (sourcePlaneProjection b e).conjTranspose = sourcePlaneProjection b e ∧
    (sourcePlaneGenerator b e).conjTranspose = -sourcePlaneGenerator b e ∧
    sourcePlaneProjection b e * sourcePlaneProjection b e = sourcePlaneProjection b e ∧
    sourcePlaneProjection b e * sourcePlaneGenerator b e = sourcePlaneGenerator b e ∧
    sourcePlaneGenerator b e * sourcePlaneProjection b e = sourcePlaneGenerator b e ∧
    sourcePlaneGenerator b e * sourcePlaneGenerator b e = -sourcePlaneProjection b e := by
  have hbb := h.source_unit
  have hee := h.direction_unit
  have hbe := h.source_direction
  have heb := h.direction_source
  simp [sourcePlaneProjection, sourcePlaneGenerator, Matrix.add_mul, Matrix.mul_add,
    Matrix.sub_mul, Matrix.mul_sub, ketBra_mul, hbb, hee, hbe, heb]
  constructor <;> abel

def sourcePlaneRotation (b e : D → ℂ) (c s : ℝ) : Matrix D D ℂ :=
  1 + (c - 1) • sourcePlaneProjection b e + s • sourcePlaneGenerator b e

theorem sourcePlaneRotation_unitary (b e : D → ℂ) (h : OrthogonalUnitPair b e)
    (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) : sourcePlaneRotation b e c s ∈ Matrix.unitaryGroup D ℂ := by
  obtain ⟨hP, hJ, hPP, hPJ, hJP, hJJ⟩ := sourcePlane_algebra b e h
  have hadj : (sourcePlaneRotation b e c s).conjTranspose =
      1 + (c - 1) • sourcePlaneProjection b e - s • sourcePlaneGenerator b e := by
    simp [sourcePlaneRotation, hP, hJ, sub_eq_add_neg]
  have hleft : (sourcePlaneRotation b e c s).conjTranspose * sourcePlaneRotation b e c s = 1 := by
    rw [hadj, sourcePlaneRotation]
    calc
      _ = 1 + (c ^ 2 + s ^ 2 - 1) • sourcePlaneProjection b e := by
        simp only [add_mul, sub_mul, mul_add, mul_sub, smul_mul_assoc, mul_smul_comm,
          one_mul, mul_one, hPP, hPJ, hJP, hJJ, smul_smul, smul_neg]
        module
      _ = 1 := by rw [hcs]; simp
  exact Matrix.mem_unitaryGroup_iff'.mpr hleft

/-- A full matrix unitary with explicit entries. -/
def sourceRotationUnitary (b e : D → ℂ) (h : OrthogonalUnitPair b e)
    (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) : Matrix.unitaryGroup D ℂ :=
  ⟨sourcePlaneRotation b e c s, sourcePlaneRotation_unitary b e h c s hcs⟩

theorem sourcePlaneRotation_prepares (b e : D → ℂ) (h : OrthogonalUnitPair b e) (c s : ℝ) :
    sourcePlaneRotation b e c s *ᵥ b = c • b + s • e := by
  simp only [sourcePlaneRotation, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    sourcePlaneProjection, sourcePlaneGenerator, Matrix.sub_mulVec, ketBra_mulVec,
    h.source_unit, h.direction_source, one_smul, zero_smul, add_zero, sub_zero]
  module

theorem sourcePlane_norms (b e : D → ℂ) (h : OrthogonalUnitPair b e) :
    ‖sourcePlaneProjection b e‖ ≤ 1 ∧ ‖sourcePlaneGenerator b e‖ ≤ 1 := by
  obtain ⟨hP, hJ, hPP, hPJ, hJP, hJJ⟩ := sourcePlane_algebra b e h
  have hp := Matrix.l2_opNorm_conjTranspose_mul_self (sourcePlaneProjection b e)
  rw [hP, hPP] at hp
  have hpn : ‖sourcePlaneProjection b e‖ ≤ 1 := by nlinarith [norm_nonneg (sourcePlaneProjection b e)]
  have hj := Matrix.l2_opNorm_conjTranspose_mul_self (sourcePlaneGenerator b e)
  rw [hJ, neg_mul, hJJ, neg_neg] at hj
  exact ⟨hpn, by nlinarith [norm_nonneg (sourcePlaneGenerator b e)]⟩

theorem sourcePlaneRotation_distance (b e : D → ℂ) (h : OrthogonalUnitPair b e) (c s : ℝ) :
    ‖sourcePlaneRotation b e c s - 1‖ ≤ |c - 1| + |s| := by
  have hp := sourcePlane_norms b e h
  have heq : sourcePlaneRotation b e c s - 1 =
      (c - 1) • sourcePlaneProjection b e + s • sourcePlaneGenerator b e := by
    unfold sourcePlaneRotation; abel
  rw [heq]
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) hp.1)
    (mul_le_of_le_one_right (abs_nonneg _) hp.2)

end OptimalQLS.LowerBounds
