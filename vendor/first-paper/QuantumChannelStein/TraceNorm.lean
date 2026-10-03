/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license; see docs/Physlib-Apache-2.0.txt.
Authors: Alex Meiburg

The SVD proof below is adapted from Physlib's
QuantumInfo/ForMathlib/MatrixNorm/TraceNorm.lean for this Lean 4.29 project.
The subsequent duality and diamond proofs are developed locally.
-/
import QuantumChannelStein.TensorNorm
import QuantumChannelStein.SpectralDecompositionCFC
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.TraceNorm
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The standard trace norm, literally the trace of the positive square root of A†A. -/
def traceNorm (A : Matrix n n ℂ) : ℝ := (CFC.sqrt (Aᴴ * A)).trace.re

omit [DecidableEq n] in
private lemma inner_A_mulVec_eq (A : Matrix n n ℂ) (v w : n → ℂ) :
    inner ℂ (WithLp.toLp 2 (A.mulVec v)) (WithLp.toLp 2 (A.mulVec w)) =
      star v ⬝ᵥ ((Aᴴ * A).mulVec w) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, Matrix.star_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.dotProduct_mulVec]

/-- Singular value decomposition for square complex matrices, with singular values expressed as
square roots of the eigenvalues of `Aᴴ * A`. -/
theorem exists_svd_sqrt_eigenvalues (A : Matrix n n ℂ) :
    let hH : (Aᴴ * A).IsHermitian := by
      simpa using (Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose)
    ∃ V W : Matrix.unitaryGroup n ℂ,
      A = V.val * Matrix.diagonal (fun i => (Real.sqrt (hH.eigenvalues i) : ℂ)) * W.valᴴ := by
  let hH : (Aᴴ * A).IsHermitian := by
    simpa using (Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose)
  let s : n → ℂ := fun i => Real.sqrt (hH.eigenvalues i)
  have hs_ne {i : n} (hi : hH.eigenvalues i ≠ 0) : s i ≠ 0 := by
    dsimp [s]
    exact_mod_cast Real.sqrt_ne_zero'.2
      (lt_of_le_of_ne (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i) (Ne.symm hi))
  let u : n → EuclideanSpace ℂ n := fun i =>
    if hi : hH.eigenvalues i ≠ 0 then
      ((s i)⁻¹ • WithLp.toLp 2 (A.mulVec (hH.eigenvectorBasis i).ofLp))
    else 0
  have hu : Orthonormal ℂ ({i | hH.eigenvalues i ≠ 0}.restrict u) := by
    rw [orthonormal_iff_ite]
    intro i j
    dsimp [u, s, Set.restrict]
    have hi' : hH.eigenvalues i.1 ≠ 0 := i.2
    have hj' : hH.eigenvalues j.1 ≠ 0 := j.2
    simp only [hi', hj', not_false_eq_true, ite_true]
    rw [inner_smul_left, inner_smul_right, inner_A_mulVec_eq, hH.mulVec_eigenvectorBasis j.1]
    by_cases hij : i.1 = j.1
    · cases Subtype.ext hij
      simp [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, mul_comm]
      field_simp [show (Real.sqrt (hH.eigenvalues i.1) : ℂ) ≠ 0 by simpa [s] using hs_ne i.2]
      exact_mod_cast (Real.sq_sqrt (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i.1)).symm
    · simpa [hij, dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
        orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal, mul_comm]
        using (show i ≠ j from fun h => hij (congrArg Subtype.val h))
  obtain ⟨b, hb⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (𝕜 := ℂ) (E := EuclideanSpace ℂ n) (ι := n)
      (by simp [finrank_euclideanSpace]) (v := u)
      (s := {i | hH.eigenvalues i ≠ 0}) hu
  let V : Matrix.unitaryGroup n ℂ := ⟨Matrix.of (fun i j ↦ b j i), by
    simp only [Matrix.mem_unitaryGroup_iff]
    ext i j
    have h1 := b.sum_inner_mul_inner (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    simp_all [inner]
    exact h1⟩
  let W : Matrix.unitaryGroup n ℂ := hH.eigenvectorUnitary
  have hAW : A * W.val = V.val * Matrix.diagonal s := by
    ext i j
    have hleft : (A * W.val) i j = A.mulVec (hH.eigenvectorBasis j).ofLp i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, W, Matrix.IsHermitian.eigenvectorUnitary_apply]
    by_cases hj : hH.eigenvalues j = 0
    · have hzero : A.mulVec (hH.eigenvectorBasis j).ofLp = 0 := by
        apply (WithLp.toLp_injective (p := 2))
        exact inner_self_eq_zero.mp (by
          rw [inner_A_mulVec_eq]
          rw [hH.mulVec_eigenvectorBasis j, hj]
          simp)
      rw [hleft, congrFun hzero i]
      simp [Matrix.mul_apply, Matrix.diagonal, V, s, hj]
    · have hbji : b j i = (s j)⁻¹ * A.mulVec (hH.eigenvectorBasis j).ofLp i := by
        simpa [u, hj] using congrArg (fun x : EuclideanSpace ℂ n => x.ofLp i) (hb j hj)
      have hs_mul : s j * b j i = A.mulVec (hH.eigenvectorBasis j).ofLp i := by
        rw [hbji]; field_simp [hs_ne hj]
      rw [hleft, ← hs_mul]; simp [Matrix.mul_apply, Matrix.diagonal, V, s, mul_comm]
  refine ⟨V, W, ?_⟩
  simpa [W, Matrix.IsHermitian.eigenvectorUnitary, Matrix.mul_assoc] using
    congrArg (fun X => X * W.valᴴ) hAW

open scoped MatrixOrder in
theorem traceNorm_eq_sum_sqrt_eigenvalues (A : Matrix n n ℂ) :
    let hH : (Aᴴ * A).IsHermitian := by
      simpa using (Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose)
    traceNorm A = ∑ i, Real.sqrt (hH.eigenvalues i) := by
  intro hH
  unfold traceNorm
  rw [CFC.sqrt_eq_real_sqrt (Aᴴ * A)
    (Matrix.nonneg_iff_posSemidef.mpr A.posSemidef_conjTranspose_mul_self),
    cfcₙ_eq_cfc, Matrix.IsHermitian.cfc_eq hH, Matrix.IsHermitian.cfc]
  simp [Matrix.trace_mul_comm, Matrix.mul_assoc]


@[simp] theorem traceNorm_zero : traceNorm (0 : Matrix n n ℂ) = 0 := by
  simp [traceNorm]

theorem traceNorm_nonneg (A : Matrix n n ℂ) : 0 ≤ traceNorm A := by
  rw [traceNorm_eq_sum_sqrt_eigenvalues]
  exact Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)

/-- Operator norm of a unitary is at most one, including the zero-dimensional case. -/
theorem unitary_opNorm_le_one (U : Matrix.unitaryGroup n ℂ) : ‖(U : Matrix n n ℂ)‖ ≤ 1 := by
  have hI := Matrix.l2_opNorm_conjTranspose_mul_self (1 : Matrix n n ℂ)
  simp only [Matrix.conjTranspose_one, Matrix.one_mul] at hI
  have hsq := Matrix.l2_opNorm_conjTranspose_mul_self (U : Matrix n n ℂ)
  rw [show (U : Matrix n n ℂ)ᴴ * U = 1 from Unitary.star_mul_self_of_mem U.property] at hsq
  have hIle : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by nlinarith [norm_nonneg (1 : Matrix n n ℂ)]
  nlinarith [norm_nonneg (U : Matrix n n ℂ)]

/-- Every entry is bounded by the genuine Hilbert operator norm. -/
theorem norm_entry_le_opNorm (A : Matrix n n ℂ) (i j : n) : ‖A i j‖ ≤ ‖A‖ := by
  let x : EuclideanSpace ℂ n := WithLp.toLp 2 (Pi.single j 1)
  have h₁ := PiLp.norm_apply_le (TensorNorm.matrixMap A x) i
  have h₂ := (TensorNorm.matrixMap A).le_opNorm x
  have hx : ‖x‖ = 1 := by simp [x]
  rw [hx, mul_one] at h₂
  have hentry : ‖A i j‖ ≤ ‖TensorNorm.matrixMap A x‖ := by
    simpa [TensorNorm.matrixMap_apply, x, Matrix.mulVec_single_one] using h₁
  exact hentry.trans h₂

/-- The trace pairing is bounded by operator norm times the standard trace norm. -/
theorem norm_trace_mul_le (K A : Matrix n n ℂ) :
    ‖(K * A).trace‖ ≤ ‖K‖ * traceNorm A := by
  let hH : (Aᴴ * A).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  obtain ⟨V, W, hA⟩ := exists_svd_sqrt_eigenvalues A
  let D : Matrix n n ℂ := Matrix.diagonal (fun i => (Real.sqrt (hH.eigenvalues i) : ℂ))
  let C : Matrix n n ℂ := (W : Matrix n n ℂ)ᴴ * K * V
  have hC : ‖C‖ ≤ ‖K‖ := by
    calc
      _ ≤ ‖(W : Matrix n n ℂ)ᴴ * K‖ * ‖(V : Matrix n n ℂ)‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖(W : Matrix n n ℂ)ᴴ‖ * ‖K‖) * ‖(V : Matrix n n ℂ)‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ ≤ (1 * ‖K‖) * 1 := by
        gcongr
        · simpa only [Matrix.l2_opNorm_conjTranspose] using unitary_opNorm_le_one W
        · exact unitary_opNorm_le_one V
      _ = ‖K‖ := by ring
  calc
    ‖(K * A).trace‖ = ‖(C * D).trace‖ := by
      congr 1
      rw [hA]
      change (K * (V.val * D * W.valᴴ)).trace = (W.valᴴ * K * V.val * D).trace
      rw [show K * (V.val * D * W.valᴴ) = (K * V.val * D) * W.valᴴ by simp [Matrix.mul_assoc],
        Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    _ ≤ ∑ i, ‖(C * D) i i‖ := by
      simpa [Matrix.trace] using norm_sum_le (s := Finset.univ) (f := fun i => (C * D) i i)
    _ = ∑ i, ‖C i i‖ * Real.sqrt (hH.eigenvalues i) := by
      simp [D, Matrix.mul_apply, Matrix.diagonal, Real.norm_eq_abs, abs_of_nonneg]
    _ ≤ ∑ i, ‖K‖ * Real.sqrt (hH.eigenvalues i) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right
        ((norm_entry_le_opNorm C i i).trans hC) (Real.sqrt_nonneg _))
    _ = ‖K‖ * traceNorm A := by rw [← Finset.mul_sum, traceNorm_eq_sum_sqrt_eigenvalues]

/-- A unitary actually attains the trace norm in the real trace pairing. -/
theorem exists_unitary_trace_eq (A : Matrix n n ℂ) :
    ∃ U : Matrix.unitaryGroup n ℂ, ((U : Matrix n n ℂ) * A).trace.re = traceNorm A := by
  let hH : (Aᴴ * A).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  obtain ⟨V, W, hA⟩ := exists_svd_sqrt_eigenvalues A
  let D : Matrix n n ℂ := Matrix.diagonal (fun i => (Real.sqrt (hH.eigenvalues i) : ℂ))
  have hVu : V.valᴴ * V.val = 1 := Unitary.star_mul_self_of_mem V.property
  have hWu : W.valᴴ * W.val = 1 := Unitary.star_mul_self_of_mem W.property
  refine ⟨W * star V, ?_⟩
  calc
    _ = D.trace.re := by
      rw [hA]
      congr 1
      change (W.val * V.valᴴ * (V.val * D * W.valᴴ)).trace = D.trace
      simp [Matrix.mul_assoc, hVu, Matrix.trace_mul_comm, hWu]
    _ = traceNorm A := by
      rw [traceNorm_eq_sum_sqrt_eigenvalues]
      simp [D, Matrix.trace]

/-- The trace-square-root definition equals the dual operator-unit-ball maximum. -/
theorem traceNorm_duality (A : Matrix n n ℂ) :
    IsGreatest {x : ℝ | ∃ K : Matrix n n ℂ, ‖K‖ ≤ 1 ∧ (K * A).trace.re = x}
      (traceNorm A) := by
  obtain ⟨U, hU⟩ := exists_unitary_trace_eq A
  refine ⟨⟨U, unitary_opNorm_le_one U, hU⟩, ?_⟩
  rintro x ⟨K, hK, rfl⟩
  exact (Complex.re_le_norm _).trans ((norm_trace_mul_le K A).trans
    (mul_le_of_le_one_left (traceNorm_nonneg A) hK))

/-- Duality yields the trace-norm triangle inequality without any norm axiom. -/
theorem traceNorm_add_le (A B : Matrix n n ℂ) :
    traceNorm (A + B) ≤ traceNorm A + traceNorm B := by
  obtain ⟨U, hU⟩ := exists_unitary_trace_eq (A + B)
  rw [← hU, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  exact add_le_add ((traceNorm_duality A).2 ⟨U, unitary_opNorm_le_one U, rfl⟩)
    ((traceNorm_duality B).2 ⟨U, unitary_opNorm_le_one U, rfl⟩)

end QuantumChannelStein.TraceNorm
