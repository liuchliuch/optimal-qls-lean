import OptimalQLS.Perturbation.MatrixLemma
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-! # Concrete block encodings with the Euclidean operator norm -/
noncomputable section
namespace OptimalQLS
open Matrix
open scoped Matrix.Norms.L2Operator
variable {S D : Type*} [Fintype S] [DecidableEq S]
  [Fintype D] [DecidableEq D] [Nonempty D]

/-- Insertion into an actual computational signal sector. -/
def signalInjection (s₀ : S) : Matrix (S × D) D ℂ :=
  Matrix.of (fun si j => if si.1 = s₀ ∧ si.2 = j then 1 else 0)

omit [Nonempty D] in
theorem signalInjection_isometry (s₀ : S) :
    (signalInjection (D := D) s₀)ᴴ * signalInjection (D := D) s₀ = 1 := by
  ext i j
  simp [Matrix.mul_apply, signalInjection, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.one_apply, ite_and, eq_comm]

theorem signalInjection_norm (s₀ : S) : ‖signalInjection (D := D) s₀‖ = 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (signalInjection (D := D) s₀)
  rw [signalInjection_isometry, norm_one] at h
  have hn := norm_nonneg (signalInjection (D := D) s₀)
  nlinarith

/-- The literal signal block, expressed as insertion, oracle, extraction. -/
def signalBlock (s₀ : S) (U : Matrix (S × D) (S × D) ℂ) : Matrix D D ℂ :=
  (signalInjection (D := D) s₀)ᴴ * U * signalInjection (D := D) s₀

omit [Nonempty D] in
theorem signalBlock_entries (s₀ : S) (U : Matrix (S × D) (S × D) ℂ) (i j : D) :
    signalBlock s₀ U i j = U (s₀,i) (s₀,j) := by
  simp [signalBlock, Matrix.mul_apply, signalInjection, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, ite_and, apply_ite]

theorem signalBlock_norm_le_one (s₀ : S) (U : Matrix.unitaryGroup (S × D) ℂ) :
    ‖signalBlock s₀ (U : Matrix (S × D) (S × D) ℂ)‖ ≤ 1 := by
  letI : Nonempty S := ⟨s₀⟩
  unfold signalBlock
  calc
    ‖(signalInjection (D := D) s₀)ᴴ * (U : Matrix (S × D) (S × D) ℂ) * signalInjection (D := D) s₀‖ ≤
        (‖(signalInjection (D := D) s₀)ᴴ‖ * ‖(U : Matrix (S × D) (S × D) ℂ)‖) *
          ‖signalInjection (D := D) s₀‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ = 1 := by rw [Matrix.l2_opNorm_conjTranspose, signalInjection_norm,
      CStarRing.norm_coe_unitary]; norm_num

/-- Definition 2.1, including the positivity and error conventions. -/
def IsBlockEncoding (s₀ : S) (α δ : ℝ) (U : Matrix.unitaryGroup (S × D) ℂ)
    (A : Matrix D D ℂ) : Prop :=
  0 < α ∧ 0 ≤ δ ∧ ‖A - α • signalBlock s₀ U‖ ≤ δ

omit [Nonempty D] in
theorem exact_block_eq {s₀ : S} {α : ℝ} {U : Matrix.unitaryGroup (S × D) ℂ}
    {A : Matrix D D ℂ} (h : IsBlockEncoding s₀ α 0 U A) :
    A = α • signalBlock s₀ U := by
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h.2.2 (norm_nonneg _)))

theorem norm_le_of_exact_block {s₀ : S} {α : ℝ} {U : Matrix.unitaryGroup (S × D) ℂ}
    {A : Matrix D D ℂ} (h : IsBlockEncoding s₀ α 0 U A) : ‖A‖ ≤ α := by
  rw [exact_block_eq h, norm_smul, Real.norm_eq_abs, abs_of_pos h.1]
  exact (mul_le_mul_of_nonneg_left (signalBlock_norm_le_one s₀ U) h.1.le).trans_eq
    (mul_one α)

/-- The solution scale used by the paper, with the actual matrix inverse. -/
def solutionScale (α : ℝ) (A : Matrix D D ℂ) (b : EuclideanSpace ℂ D) : ℝ :=
  α * ‖Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (Ring.inverse A) b‖

theorem solutionScale_bounds {s₀ : S} {α κ : ℝ}
    {U : Matrix.unitaryGroup (S × D) ℂ} {A : Matrix D D ℂ}
    (henc : IsBlockEncoding s₀ α 0 U A) (hA : IsUnit A)
    (hκ : α * ‖Ring.inverse A‖ ≤ κ) (b : EuclideanSpace ℂ D) (hb : ‖b‖ = 1) :
    1 ≤ solutionScale α A b ∧ solutionScale α A b ≤ κ := by
  let φ := Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)
  have hφA : IsUnit (φ A) := hA.map φ.toMonoidHom
  have hinv := Perturbation.toEuclideanCLM_inverse A hA
  have heq : φ A (φ (Ring.inverse A) b) = b := by
    rw [hinv]
    exact Perturbation.apply_inverse (φ A) hφA b
  constructor
  · calc
      1 = ‖φ A (φ (Ring.inverse A) b)‖ := by rw [heq, hb]
      _ ≤ ‖φ A‖ * ‖φ (Ring.inverse A) b‖ := (φ A).le_opNorm _
      _ ≤ α * ‖φ (Ring.inverse A) b‖ :=
        mul_le_mul_of_nonneg_right (norm_le_of_exact_block henc) (norm_nonneg _)
  · have hnorm := (φ (Ring.inverse A)).le_opNorm b
    rw [hb, mul_one] at hnorm
    exact (mul_le_mul_of_nonneg_left hnorm henc.1.le).trans hκ

end OptimalQLS
