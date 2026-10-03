import QuantumChannelStein.Kraus
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Reference extension preserves the Hilbert operator norm

All matrix norms in this file are the L2 operator norm supplied by
`Matrix.Norms.L2Operator`, not the entrywise or row-sum matrix norms.
The reference factor is an arbitrary finite type, including the empty type.
-/

noncomputable section
namespace QuantumChannelStein.TensorNorm

open scoped BigOperators Kronecker Matrix.Norms.L2Operator
open Matrix WithLp

variable {r m n : Type*} [Fintype r] [DecidableEq r]
  [Fintype m] [Fintype n] [DecidableEq n]

/-- A slice at a fixed reference coordinate, with its Euclidean norm. -/
def slice (x : EuclideanSpace ℂ (r × n)) (i : r) : EuclideanSpace ℂ n :=
  toLp 2 (fun j => x (i, j))

omit [DecidableEq r] [DecidableEq n] in
/-- The squared norm splits as the sum of squared norms of reference slices. -/
theorem norm_sq_eq_sum_slice (x : EuclideanSpace ℂ (r × n)) :
    ‖x‖ ^ 2 = ∑ i, ‖slice x i‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, slice, PiLp.toLp_apply,
    Fintype.sum_prod_type]

omit [Fintype m] [DecidableEq n] in
/-- Acting by `I ⊗ C` applies `C` independently on each reference slice. -/
theorem one_kronecker_mulVec_apply (C : Matrix m n ℂ)
    (x : r × n → ℂ) (i : r) (a : m) :
    (((1 : Matrix r r ℂ) ⊗ₖ C) *ᵥ x) (i, a) =
      (C *ᵥ (fun j => x (i, j))) a := by
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply, Fintype.sum_prod_type]

/-- Extending a rectangular matrix by the identity reference does not increase
its action bound on Hilbert space. -/
theorem one_kronecker_mulVec_norm_le (C : Matrix m n ℂ)
    (x : EuclideanSpace ℂ (r × n)) :
    ‖toLp 2 (((1 : Matrix r r ℂ) ⊗ₖ C) *ᵥ ofLp x)‖ ≤ ‖C‖ * ‖x‖ := by
  classical
  let y : EuclideanSpace ℂ (r × m) :=
    toLp 2 (((1 : Matrix r r ℂ) ⊗ₖ C) *ᵥ ofLp x)
  have hs : ∀ i, ‖slice y i‖ ≤ ‖C‖ * ‖slice x i‖ := by
    intro i
    convert Matrix.l2_opNorm_mulVec C (slice x i) using 1
    congr 1
    ext a
    exact one_kronecker_mulVec_apply C (ofLp x) i a
  have hsq : ‖y‖ ^ 2 ≤ (‖C‖ * ‖x‖) ^ 2 := by
    rw [norm_sq_eq_sum_slice y, mul_pow, norm_sq_eq_sum_slice x,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (slice y i)) (hs i) 2
  exact (sq_le_sq₀ (norm_nonneg y) (mul_nonneg (norm_nonneg C) (norm_nonneg x))).mp hsq

/-- Tensoring with an identity of any finite size does not increase the
Hilbert operator norm. This includes an empty reference space. -/
theorem one_kronecker_opNorm_le (C : Matrix m n ℂ) :
    ‖(1 : Matrix r r ℂ) ⊗ₖ C‖ ≤ ‖C‖ := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg C)
  intro x
  exact one_kronecker_mulVec_norm_le C x

/-- Embed a vector into one reference coordinate. -/
def atReference (i : r) (x : EuclideanSpace ℂ n) : EuclideanSpace ℂ (r × n) :=
  toLp 2 (fun p => if p.1 = i then x p.2 else 0)

omit [DecidableEq n] in
/-- The coordinate embedding is a Hilbert-space isometry. -/
theorem atReference_norm (i : r) (x : EuclideanSpace ℂ n) :
    ‖atReference i x‖ = ‖x‖ := by
  simp [EuclideanSpace.norm_eq, atReference, Fintype.sum_prod_type, apply_ite]

omit [Fintype m] [DecidableEq n] in
/-- Reference extension intertwines the coordinate embedding with the original
matrix action. -/
theorem one_kronecker_mulVec_atReference (C : Matrix m n ℂ)
    (i : r) (x : EuclideanSpace ℂ n) :
    toLp 2 (((1 : Matrix r r ℂ) ⊗ₖ C) *ᵥ ofLp (atReference i x)) =
      atReference i (toLp 2 (C *ᵥ ofLp x)) := by
  ext ⟨j, a⟩
  simp only [PiLp.toLp_apply, one_kronecker_mulVec_apply, atReference,
    ofLp_toLp]
  by_cases h : j = i
  · simp [h, Matrix.mulVec, dotProduct]
  · simp [h, Matrix.mulVec, dotProduct]

/-- Tensoring with a nonzero finite reference space preserves the Hilbert
operator norm exactly. -/
theorem one_kronecker_opNorm [Nonempty r] (C : Matrix m n ℂ) :
    ‖(1 : Matrix r r ℂ) ⊗ₖ C‖ = ‖C‖ := by
  classical
  apply le_antisymm (one_kronecker_opNorm_le C)
  rw [Matrix.l2_opNorm_def C]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  let i : r := Classical.choice inferInstance
  have h := Matrix.l2_opNorm_mulVec ((1 : Matrix r r ℂ) ⊗ₖ C) (atReference i x)
  change ‖toLp 2 (((1 : Matrix r r ℂ) ⊗ₖ C) *ᵥ ofLp (atReference i x))‖ ≤
    ‖(1 : Matrix r r ℂ) ⊗ₖ C‖ * ‖atReference i x‖ at h
  rw [one_kronecker_mulVec_atReference, atReference_norm, atReference_norm] at h
  exact h

/-- Swap the two finite coordinates of a Euclidean vector. -/
def swap (x : EuclideanSpace ℂ (r × n)) : EuclideanSpace ℂ (n × r) :=
  toLp 2 (fun p => x (p.2, p.1))

omit [DecidableEq r] [DecidableEq n] in
/-- Coordinate swapping is a Hilbert-space isometry. -/
theorem swap_norm (x : EuclideanSpace ℂ (r × n)) : ‖swap x‖ = ‖x‖ := by
  simp only [EuclideanSpace.norm_eq, swap, PiLp.toLp_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

omit [Fintype m] [DecidableEq n] in
/-- An identity on the right leaves each environment coordinate separate. -/
theorem kronecker_one_mulVec_apply (C : Matrix m n ℂ)
    (x : n × r → ℂ) (a : m) (i : r) :
    ((C ⊗ₖ (1 : Matrix r r ℂ)) *ᵥ x) (a, i) =
      (C *ᵥ (fun j => x (j, i))) a := by
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply, Fintype.sum_prod_type]

omit [Fintype m] [DecidableEq n] in
/-- Swapping coordinates interchanges left and right reference extension. -/
theorem swap_kronecker_one_mulVec (C : Matrix m n ℂ)
    (x : EuclideanSpace ℂ (n × r)) :
    swap (toLp 2 ((C ⊗ₖ (1 : Matrix r r ℂ)) *ᵥ ofLp x)) =
      toLp 2 (((1 : Matrix r r ℂ) ⊗ₖ C) *ᵥ ofLp (swap x)) := by
  ext ⟨i, a⟩
  simp [swap, kronecker_one_mulVec_apply, one_kronecker_mulVec_apply]

/-- Identity extension on the right has the same Hilbert action bound. -/
theorem kronecker_one_mulVec_norm_le (C : Matrix m n ℂ)
    (x : EuclideanSpace ℂ (n × r)) :
    ‖toLp 2 ((C ⊗ₖ (1 : Matrix r r ℂ)) *ᵥ ofLp x)‖ ≤ ‖C‖ * ‖x‖ := by
  classical
  have h := one_kronecker_mulVec_norm_le C (swap x)
  rw [← swap_kronecker_one_mulVec, swap_norm, swap_norm] at h
  exact h

/-- Identity extension on the right does not increase the L2 operator norm. -/
theorem kronecker_one_opNorm_le (C : Matrix m n ℂ) :
    ‖C ⊗ₖ (1 : Matrix r r ℂ)‖ ≤ ‖C‖ := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg C)
  exact kronecker_one_mulVec_norm_le C

/-- The continuous linear action of a rectangular matrix on Euclidean spaces. -/
def matrixMap (A : Matrix m n ℂ) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ m :=
  (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A

@[simp] theorem matrixMap_apply (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    matrixMap A x = toLp 2 (A *ᵥ ofLp x) := rfl

/-- This map carries precisely the L2 operator norm used throughout this file. -/
@[simp] theorem matrixMap_norm (A : Matrix m n ℂ) : ‖matrixMap A‖ = ‖A‖ := rfl

variable {k : Type*} [Fintype k] [DecidableEq k]

@[simp] theorem matrixMap_mul (A : Matrix m n ℂ) (B : Matrix n k ℂ) :
    matrixMap (A * B) = (matrixMap A).comp (matrixMap B) := by
  ext x i
  simp [matrixMap_apply, Matrix.mulVec_mulVec]

/-- Operators on separate tensor factors commute, even when the second
operator is rectangular and changes the environment dimension. -/
theorem tensor_factors_commute (T : Matrix r r ℂ) (C : Matrix m n ℂ)
    [DecidableEq m] :
    (T ⊗ₖ (1 : Matrix m m ℂ)) * ((1 : Matrix r r ℂ) ⊗ₖ C) =
      ((1 : Matrix r r ℂ) ⊗ₖ C) * (T ⊗ₖ (1 : Matrix n n ℂ)) := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

/-- Hilbert-space acceptance-amplitude estimate: apply a contraction on the
observable factor and an arbitrary rectangular comparison operator on the
environment factor. The error is measured before the observable contraction.

This is the norm estimate needed in Lemma 3.4, separately from the Born-rule
identification of its amplitudes with square roots of acceptance probabilities. -/
theorem tensor_amplitude_le (T : Matrix r r ℂ) (C : Matrix m n ℂ)
    [DecidableEq m] (x : EuclideanSpace ℂ (r × m))
    (y : EuclideanSpace ℂ (r × n)) (error : ℝ)
    (hT : ‖T‖ ≤ 1)
    (herror : ‖x - matrixMap ((1 : Matrix r r ℂ) ⊗ₖ C) y‖ ≤ error) :
    ‖matrixMap (T ⊗ₖ (1 : Matrix m m ℂ)) x‖ ≤
      ‖C‖ * ‖matrixMap (T ⊗ₖ (1 : Matrix n n ℂ)) y‖ + error := by
  let A := matrixMap (T ⊗ₖ (1 : Matrix m m ℂ))
  let B := matrixMap ((1 : Matrix r r ℂ) ⊗ₖ C)
  let D := matrixMap (T ⊗ₖ (1 : Matrix n n ℂ))
  have hA : ‖A‖ ≤ 1 := (matrixMap_norm _).trans_le ((kronecker_one_opNorm_le T).trans hT)
  have hB : ‖B‖ ≤ ‖C‖ := (matrixMap_norm _).trans_le (one_kronecker_opNorm_le C)
  have hcomm : A (B y) = B (D y) := by
    have h := congrArg (fun M : Matrix (r × m) (r × n) ℂ => matrixMap M y)
      (tensor_factors_commute T C)
    simpa only [matrixMap_mul, ContinuousLinearMap.comp_apply] using h
  have hdiff : ‖A x - A (B y)‖ ≤ error := by
    rw [← map_sub]
    simpa only [one_mul] using A.le_of_opNorm_le_of_le hA herror
  calc
    ‖A x‖ ≤ ‖A (B y)‖ + ‖A x - A (B y)‖ := norm_le_insert' _ _
    _ ≤ ‖B (D y)‖ + error := add_le_add (le_of_eq (congrArg norm hcomm)) hdiff
    _ ≤ ‖C‖ * ‖D y‖ + error := add_le_add (B.le_of_opNorm_le hB _) le_rfl

@[simp] theorem matrixMap_sub (A B : Matrix m n ℂ) :
    matrixMap (A - B) = matrixMap A - matrixMap B := by
  exact (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap).map_sub A B

/-- An L2 operator approximation of two dilation matrices implies the
acceptance-amplitude bound uniformly over the Euclidean unit ball. The
isometry and channel interpretation of the matrices is not needed for this
analytic implication. -/
theorem tensor_amplitude_le_of_operator_approx (T : Matrix r r ℂ)
    (C : Matrix m n ℂ) [DecidableEq m]
    (U : Matrix (r × m) k ℂ) (V : Matrix (r × n) k ℂ)
    (z : EuclideanSpace ℂ k) (error : ℝ)
    (hT : ‖T‖ ≤ 1) (hz : ‖z‖ ≤ 1)
    (happrox : ‖U - ((1 : Matrix r r ℂ) ⊗ₖ C) * V‖ ≤ error) :
    ‖matrixMap (T ⊗ₖ (1 : Matrix m m ℂ)) (matrixMap U z)‖ ≤
      ‖C‖ * ‖matrixMap (T ⊗ₖ (1 : Matrix n n ℂ)) (matrixMap V z)‖ + error := by
  apply tensor_amplitude_le T C (matrixMap U z) (matrixMap V z) error hT
  have hnorm : ‖matrixMap (U - ((1 : Matrix r r ℂ) ⊗ₖ C) * V)‖ ≤ error := by
    rwa [matrixMap_norm]
  have h := (matrixMap (U - ((1 : Matrix r r ℂ) ⊗ₖ C) * V)).le_of_opNorm_le_of_le
    hnorm hz
  simpa only [matrixMap_sub, matrixMap_mul, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, mul_one] using h

end QuantumChannelStein.TensorNorm
