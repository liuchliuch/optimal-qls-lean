import OptimalQLS.Transduction.Core
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Coordinate-level form of universal transduction, for arbitrary finite public
and private index types. This adapter uses the sum/product *isometry*. -/
noncomputable section
namespace OptimalQLS.Transduction

open Matrix
open scoped InnerProductSpace
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A unitary matrix acts as an actual Hilbert-space isometric equivalence. -/
def matrixIsometry {n : Type*} [Fintype n] [DecidableEq n]
    (S : Matrix.unitaryGroup n ℂ) : EuclideanSpace ℂ n ≃ₗᵢ[ℂ] EuclideanSpace ℂ n :=
  Unitary.linearIsometryEquiv
    ⟨Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (S : Matrix n n ℂ),
      Unitary.map_mem (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) S.property⟩

@[simp] theorem matrixIsometry_apply {n : Type*} [Fintype n] [DecidableEq n]
    (S : Matrix.unitaryGroup n ℂ) (x : n → ℂ) :
    matrixIsometry S (WithLp.toLp 2 x) = WithLp.toLp 2 ((S : Matrix n n ℂ) *ᵥ x) := rfl

/-- Matrix form of a Hilbert-space unitary. -/
def isometryMatrix {n : Type*} [Fintype n] [DecidableEq n]
    (U : EuclideanSpace ℂ n ≃ₗᵢ[ℂ] EuclideanSpace ℂ n) : Matrix.unitaryGroup n ℂ :=
  ⟨(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).symm
      (Unitary.linearIsometryEquiv.symm U : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n),
    Unitary.map_mem (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).symm
      (Unitary.linearIsometryEquiv.symm U).property⟩

@[simp] theorem isometryMatrix_apply {n : Type*} [Fintype n] [DecidableEq n]
    (U : EuclideanSpace ℂ n ≃ₗᵢ[ℂ] EuclideanSpace ℂ n) (x : n → ℂ) :
    (isometryMatrix U : Matrix n n ℂ) *ᵥ x = WithLp.ofLp (U (WithLp.toLp 2 x)) := by
  have h : Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (isometryMatrix U : Matrix n n ℂ) =
      (U : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) := by
    simp [isometryMatrix]
  exact congrArg WithLp.ofLp (congrArg (fun f : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n => f (WithLp.toLp 2 x)) h)

/-- The coordinate splitting respects the L² norm on both sides. -/
def sumIsometry : EuclideanSpace ℂ (ι ⊕ κ) ≃ₗᵢ[ℂ]
    HilbertSum (EuclideanSpace ℂ ι) (EuclideanSpace ℂ κ) :=
  PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : ι ⊕ κ => ℂ)

@[simp] theorem sumIsometry_pair (x : ι → ℂ) (w : κ → ℂ) :
    sumIsometry (WithLp.toLp 2 (Sum.elim x w)) =
      pair (WithLp.toLp 2 x) (WithLp.toLp 2 w) := rfl

@[simp] theorem sumIsometry_symm_pair (x : ι → ℂ) (w : κ → ℂ) :
    sumIsometry.symm (pair (WithLp.toLp 2 x) (WithLp.toLp 2 w)) =
      WithLp.toLp 2 (Sum.elim x w) := rfl

/-- The supplied matrix unitary transported to the Hilbert direct sum. -/
def matrixTransducer (S : Matrix.unitaryGroup (ι ⊕ κ) ℂ) :
    HilbertSum (EuclideanSpace ℂ ι) (EuclideanSpace ℂ κ) ≃ₗᵢ[ℂ]
      HilbertSum (EuclideanSpace ℂ ι) (EuclideanSpace ℂ κ) :=
  sumIsometry.symm.trans ((matrixIsometry S).trans sumIsometry)

/-- The public matrix is constructed, not supplied as a hypothesis. -/
def publicMatrix (S : Matrix.unitaryGroup (ι ⊕ κ) ℂ) : Matrix.unitaryGroup ι ℂ :=
  isometryMatrix (publicAction (H := EuclideanSpace ℂ ι) (L := EuclideanSpace ℂ κ) (matrixTransducer S))

/-- Canonical minimum-norm catalyst, in private coordinates. -/
def matrixCatalyst (S : Matrix.unitaryGroup (ι ⊕ κ) ℂ) (x : ι → ℂ) : κ → ℂ :=
  WithLp.ofLp (catalyst (H := EuclideanSpace ℂ ι) (L := EuclideanSpace ℂ κ) (matrixTransducer S) (WithLp.toLp 2 x))

/-- Exact coordinate form of the general transduction equation. -/
theorem matrix_transduction_eq (S : Matrix.unitaryGroup (ι ⊕ κ) ℂ) (x : ι → ℂ) :
    (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) *ᵥ Sum.elim x (matrixCatalyst S x) =
      Sum.elim ((publicMatrix S : Matrix ι ι ℂ) *ᵥ x) (matrixCatalyst S x) := by
  have h := transduction_eq (H := EuclideanSpace ℂ ι) (L := EuclideanSpace ℂ κ) (matrixTransducer S) (WithLp.toLp 2 x)
  have hh := congrArg (fun z => WithLp.ofLp (sumIsometry.symm z)) h
  simpa [matrixTransducer, publicMatrix, matrixCatalyst, LinearIsometryEquiv.trans_apply,
    ← sumIsometry_pair] using hh

/-- Definition 2.6 background theorem, directly on arbitrary finite matrix sectors. -/
theorem public_action_exists (S : Matrix.unitaryGroup (ι ⊕ κ) ℂ) :
    ∃ U : Matrix.unitaryGroup ι ℂ, ∀ x : ι → ℂ, ∃ w : κ → ℂ,
      (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) *ᵥ Sum.elim x w =
        Sum.elim ((U : Matrix ι ι ℂ) *ᵥ x) w :=
  ⟨publicMatrix S, fun x => ⟨matrixCatalyst S x, matrix_transduction_eq S x⟩⟩

end OptimalQLS.Transduction
