import OptimalQLS.PolynomialTransform.CleanEmbedding
import OptimalQLS.Problem
import Mathlib.Data.Nat.Log

/-! Literal computational zero-padding; no choice of oracle extension occurs here. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace OptimalQLS.PhysicalPadding
open Matrix PolynomialTransform
open scoped BigOperators Matrix.Norms.L2Operator

/-- The exact number of data qubits, i.e. the ceiling base-two logarithm. -/
def dataQubits (d : ℕ) : ℕ := Nat.clog 2 d
/-- The entire physical computational data register. -/
def physicalDimension (d : ℕ) : ℕ := 2 ^ dataQubits d

instance (d : ℕ) : NeZero (physicalDimension d) := ⟨by unfold physicalDimension; positivity⟩

theorem dimension_le_physicalDimension (d : ℕ) : d ≤ physicalDimension d :=
  Nat.le_pow_clog (by decide) d

/-- The fixed initial-segment inclusion, in the actual computational basis. -/
def activeIndex (d : ℕ) : Fin d ↪ Fin (physicalDimension d) :=
  ⟨Fin.castLE (dimension_le_physicalDimension d), Fin.castLE_injective _⟩

@[simp] theorem activeIndex_val (d : ℕ) (i : Fin d) : (activeIndex d i).val = i.val := rfl
@[simp] theorem activeIndex_zero (d : ℕ) [NeZero d] : activeIndex d 0 = 0 := rfl

theorem physicalDimension_lt_twice {d : ℕ} (hd : 0 < d) : physicalDimension d < 2*d := by
  by_cases h : d = 1
  · subst d; norm_num [physicalDimension, dataQubits]
  have hd1 : 1 < d := by omega
  have hp := Nat.pow_pred_clog_lt_self (b := 2) (by decide) hd1
  have hc : 0 < Nat.clog 2 d := Nat.clog_pos (by decide) hd1
  unfold physicalDimension dataQubits
  calc
    2 ^ Nat.clog 2 d = 2 * 2 ^ (Nat.clog 2 d - 1) := by
      conv_lhs => rw [show Nat.clog 2 d = (Nat.clog 2 d - 1) + 1 by omega]
      rw [pow_succ]; omega
    _ < 2*d := Nat.mul_lt_mul_of_pos_left hp (by decide)

section General
variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

abbrev insertion (f : D ↪ P) : Matrix P D ℂ := basisInsertion f

@[simp] theorem insertion_adjoint_mul (f : D ↪ P) : (insertion f)ᴴ * insertion f = 1 :=
  basisInsertion_isometry f f.injective

/-- Coordinate restriction is the adjoint computational inclusion. -/
def restriction (f : D ↪ P) : EuclideanSpace ℂ P →L[ℂ] EuclideanSpace ℂ D :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i => x (f i))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

@[simp] theorem restriction_apply (f : D ↪ P) (x : EuclideanSpace ℂ P) (i : D) :
    restriction f x i = x (f i) := rfl

@[simp] theorem insertion_mulVec_active (f : D ↪ P) (x : D → ℂ) (i : D) :
    (insertion f *ᵥ x) (f i) = x i := by
  simp [insertion, basisInsertion, Matrix.mulVec, dotProduct, f.injective.eq_iff]

@[simp] theorem insertion_mulVec_inactive (f : D ↪ P) (x : D → ℂ) (p : P)
    (hp : p ∉ Set.range f) : (insertion f *ᵥ x) p = 0 := by
  have hh : ∀ i, p ≠ f i := by simpa [Set.mem_range, eq_comm] using hp
  simp [insertion, basisInsertion, Matrix.mulVec, dotProduct, hh]

theorem insertion_inner (f : D ↪ P) (x : EuclideanSpace ℂ D) (y : EuclideanSpace ℂ P) :
    inner ℂ (Matrix.toEuclideanLin (insertion f) x) y = inner ℂ x (restriction f y) := by
  simp only [PiLp.inner_apply, Matrix.toEuclideanLin_apply, PiLp.toLp_apply,
    Matrix.mulVec, dotProduct, RCLike.inner_apply, map_sum, starRingEnd_apply,
    insertion, basisInsertion, map_mul, apply_ite, star_one, star_zero]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp [mul_ite, ite_mul]

/-- Literal zero insertion is an actual Hilbert-space isometry. -/
def coordinateIsometry (f : D ↪ P) : EuclideanSpace ℂ D →ₗᵢ[ℂ] EuclideanSpace ℂ P where
  toLinearMap := Matrix.toEuclideanLin (insertion f)
  norm_map' x := by
    have hi := insertion_inner f x (Matrix.toEuclideanLin (insertion f) x)
    have hr : restriction f (Matrix.toEuclideanLin (insertion f) x) = x := by
      ext i
      exact insertion_mulVec_active f _ i
    rw [hr] at hi
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hi
    have hh : ‖Matrix.toEuclideanLin (insertion f) x‖ ^ 2 = ‖x‖ ^ 2 := by exact_mod_cast hi
    nlinarith [norm_nonneg (Matrix.toEuclideanLin (insertion f) x), norm_nonneg x]

@[simp] theorem coordinateIsometry_apply (f : D ↪ P) (x : EuclideanSpace ℂ D) (p : P) :
    coordinateIsometry f x p = (insertion f *ᵥ WithLp.ofLp x) p := rfl

@[simp] theorem restriction_isometry (f : D ↪ P) (x : EuclideanSpace ℂ D) :
    restriction f (coordinateIsometry f x) = x := by
  ext i
  exact insertion_mulVec_active f _ i

theorem coordinateIsometry_inner (f : D ↪ P) (x : EuclideanSpace ℂ D)
    (y : EuclideanSpace ℂ P) :
    inner ℂ (coordinateIsometry f x) y = inner ℂ x (restriction f y) :=
  insertion_inner f x y

/-- Fully zero-extended square matrix, including every unused row and column. -/
def zeroExtend (f : D ↪ P) (A : Matrix D D ℂ) : Matrix P P ℂ :=
  insertion f * A * (insertion f)ᴴ

@[simp] theorem zeroExtend_intertwines (f : D ↪ P) (A : Matrix D D ℂ) :
    zeroExtend f A * insertion f = insertion f * A := by
  simp [zeroExtend, Matrix.mul_assoc]

@[simp] theorem zeroExtend_adjoint_intertwines (f : D ↪ P) (A : Matrix D D ℂ) :
    (insertion f)ᴴ * zeroExtend f A = A * (insertion f)ᴴ := by
  simp [zeroExtend, ← Matrix.mul_assoc]

@[simp] theorem zeroExtend_compression (f : D ↪ P) (A : Matrix D D ℂ) :
    (insertion f)ᴴ * zeroExtend f A * insertion f = A := by
  rw [zeroExtend_adjoint_intertwines, Matrix.mul_assoc, insertion_adjoint_mul, Matrix.mul_one]

theorem zeroExtend_hermitian (f : D ↪ P) (A : Matrix D D ℂ) (hA : A.IsHermitian) :
    (zeroExtend f A).IsHermitian := by
  simp only [Matrix.IsHermitian, zeroExtend, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  rw [hA]
  exact (Matrix.mul_assoc ..).symm

theorem insertion_norm (f : D ↪ P) [Nonempty D] : ‖insertion f‖ = 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (insertion f)
  rw [insertion_adjoint_mul, norm_one] at h
  nlinarith [norm_nonneg (insertion f)]

theorem zeroExtend_norm (f : D ↪ P) [Nonempty D] (A : Matrix D D ℂ) :
    ‖zeroExtend f A‖ = ‖A‖ := by
  have hJ := insertion_norm f
  have hJ' : ‖(insertion f)ᴴ‖ = 1 := by rw [Matrix.l2_opNorm_conjTranspose, hJ]
  apply le_antisymm
  · calc
      ‖zeroExtend f A‖ ≤ ‖insertion f * A‖ * ‖(insertion f)ᴴ‖ := Matrix.l2_opNorm_mul ..
      _ ≤ (‖insertion f‖ * ‖A‖) * ‖(insertion f)ᴴ‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul ..) (norm_nonneg _)
      _ = ‖A‖ := by rw [hJ, hJ']; ring
  · calc
      ‖A‖ = ‖(insertion f)ᴴ * zeroExtend f A * insertion f‖ := by rw [zeroExtend_compression]
      _ ≤ ‖(insertion f)ᴴ * zeroExtend f A‖ * ‖insertion f‖ := Matrix.l2_opNorm_mul ..
      _ ≤ (‖(insertion f)ᴴ‖ * ‖zeroExtend f A‖) * ‖insertion f‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul ..) (norm_nonneg _)
      _ = ‖zeroExtend f A‖ := by rw [hJ, hJ']; ring

end General

abbrev activeIsometry (d : ℕ) := coordinateIsometry (activeIndex d)
abbrev physicalMatrix {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) := zeroExtend (activeIndex d) A

end OptimalQLS.PhysicalPadding
