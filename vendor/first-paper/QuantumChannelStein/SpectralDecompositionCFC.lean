import QuantumChannelStein.RelativeEntropy
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! # Functional calculus in an explicitly prescribed eigenbasis -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SpectralDecomposition

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Diagonal functional calculus transported through a prescribed unitary. -/
def diagonalHom (U : Matrix.unitaryGroup ι ℂ) : (ι → ℂ) →⋆ₐ[ℂ] Matrix ι ι ℂ where
  toFun d := (U : Matrix ι ι ℂ) * Matrix.diagonal d * (U : Matrix ι ι ℂ)ᴴ
  map_zero' := by simp [Pi.zero_def]
  map_one' := by simp [Pi.one_def, ← Matrix.star_eq_conjTranspose]
  map_add' f g := by
    simp only [← Matrix.add_mul, ← Matrix.mul_add, Matrix.diagonal_add]
    rfl
  map_mul' f g := by
    have reassoc {a b c d e f : Matrix ι ι ℂ} :
        (a * b * c) * (d * e * f) = a * (b * (c * d) * e) * f := by
      simp only [mul_assoc]
    simp only [reassoc, ← Matrix.star_eq_conjTranspose, unitary.coe_star_mul_self,
      Matrix.mul_one, Matrix.diagonal_mul_diagonal, Pi.mul_def]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    change (U : Matrix ι ι ℂ) * Matrix.diagonal (c • (1 : ι → ℂ)) *
      (U : Matrix ι ι ℂ)ᴴ = c • 1
    rw [Matrix.diagonal_smul]
    simp only [Pi.one_def, Matrix.diagonal_one]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    have hu : (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ)ᴴ = 1 :=
      unitary.mul_star_self_of_mem U.property
    rw [hu]
  map_star' f := by
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_assoc]

theorem diagonalHom_continuous (U : Matrix.unitaryGroup ι ℂ) : Continuous (diagonalHom U) := by
  change Continuous (fun d => (U : Matrix ι ι ℂ) * Matrix.diagonal d * (U : Matrix ι ι ℂ)ᴴ)
  fun_prop

/-- The continuous functional calculus can be evaluated in any prescribed
unitary eigenbasis, including at repeated and zero eigenvalues. -/
theorem cfc_of_unitary_diagonalization (U : Matrix.unitaryGroup ι ℂ)
    (d : ι → ℝ) (f : ℝ → ℝ) :
    cfc f ((U : Matrix ι ι ℂ) * Matrix.diagonal (fun i => (d i : ℂ)) *
      (U : Matrix ι ι ℂ)ᴴ) =
    (U : Matrix ι ι ℂ) * Matrix.diagonal (fun i => (f (d i) : ℂ)) *
      (U : Matrix ι ι ℂ)ᴴ := by
  let a : ι → ℂ := fun i => (d i : ℂ)
  have ha : IsSelfAdjoint a := by
    change star a = a
    ext i
    simp [a]
  have hai (i : ι) : IsSelfAdjoint (a i) := by
    change star (a i) = a i
    simp [a]
  have hs : (spectrum ℝ a).Finite := by
    rw [Pi.spectrum_eq]
    apply Set.finite_iUnion
    intro i
    exact (Set.finite_singleton (d i)).subset (CFC.spectrum_algebraMap_subset (A := ℂ) (d i))
  have hf : ContinuousOn f (spectrum ℝ a) := hs.continuousOn f
  have hout : IsSelfAdjoint (diagonalHom U a) := by
    change star (diagonalHom U a) = diagonalHom U a
    rw [← map_star, ha.star_eq]
  have heval : cfc f a = fun i => (f (d i) : ℂ) := by
    rw [cfc_map_pi (S := ℂ) f a (by rwa [← Pi.spectrum_eq]) ha hai]
    funext i
    exact cfc_algebraMap (A := ℂ) (d i) f
  have h := (diagonalHom U).map_cfc f a hf (diagonalHom_continuous U) ha hout
  rw [heval] at h
  exact h.symm

/-- Bijective coordinate relabeling as a star algebra homomorphism. -/
def reindexHom {κ : Type*} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) :
    Matrix ι ι ℂ →⋆ₐ[ℂ] Matrix κ κ ℂ where
  __ := (Matrix.reindexAlgEquiv ℂ ℂ e).toAlgHom
  map_star' A := (Matrix.conjTranspose_reindex e e A).symm

/-- Real functional calculus is invariant under a simultaneous bijective
relabeling of matrix rows and columns. -/
theorem cfc_reindex {κ : Type*} [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f (Matrix.reindex e e A) = Matrix.reindex e e (cfc f A) := by
  have hf : ContinuousOn f (spectrum ℝ A) := by
    rw [hA.spectrum_real_eq_range_eigenvalues]
    exact (Set.finite_range _).continuousOn f
  have hcont : Continuous (reindexHom e) := by
    change Continuous (fun A : Matrix ι ι ℂ => A.submatrix e.symm e.symm)
    fun_prop
  exact ((reindexHom e).map_cfc f A hf hcont hA.isSelfAdjoint
    (hA.submatrix e.symm).isSelfAdjoint).symm

/-- A CFC cross trace in any prescribed unitary eigenbasis. -/
theorem trace_mul_cfc_diagonalization (X : Matrix ι ι ℂ)
    (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℝ) (f : ℝ → ℝ) :
    (X * cfc f ((U : Matrix ι ι ℂ) * Matrix.diagonal (fun i => (d i : ℂ)) *
      (U : Matrix ι ι ℂ)ᴴ)).trace =
      ∑ i, (((U : Matrix ι ι ℂ)ᴴ * X * (U : Matrix ι ι ℂ)) i i) * (f (d i) : ℂ) := by
  rw [cfc_of_unitary_diagonalization, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.trace_mul_cycle]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal, Matrix.mul_assoc]

/-- Unitary conjugation preserves the trace. -/
theorem trace_unitary_conjugate (U : Matrix.unitaryGroup ι ℂ) (X : Matrix ι ι ℂ) :
    ((U : Matrix ι ι ℂ)ᴴ * X * (U : Matrix ι ι ℂ)).trace = X.trace := by
  rw [Matrix.trace_mul_cycle]
  have hU : (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ)ᴴ = 1 :=
    unitary.mul_star_self_of_mem U.property
  rw [hU, Matrix.one_mul]

end QuantumChannelStein.SpectralDecomposition
