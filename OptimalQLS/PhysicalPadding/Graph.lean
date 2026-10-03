import OptimalQLS.PhysicalPadding.Operators
import OptimalQLS.Preparation.GraphPromises

/-! Active data transport for the physical graph. The off-diagonal identity is
on the full physical register; the graph itself is not zero-extended. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000
namespace OptimalQLS.PhysicalPadding
open Matrix Polynomial PolynomialTransform GraphEncoding Preparation
open scoped BigOperators Matrix.Norms.L2Operator
variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

def graphIndex (f : D ↪ P) : (Fin 4 × D) ↪ (Fin 4 × P) :=
  (Function.Embedding.refl (Fin 4)).prodMap f

@[simp] theorem graphIndex_apply (f : D ↪ P) (g : Fin 4) (i : D) :
    graphIndex f (g,i) = (g,f i) := rfl

abbrev graphIsometry (f : D ↪ P) := coordinateIsometry (graphIndex f)
abbrev graphRestriction (f : D ↪ P) := restriction (graphIndex f)

theorem graph_intertwines (f : D ↪ P) (A : Matrix D D ℂ) (κ : ℝ) :
    graphMatrix (zeroExtend f A) κ * insertion (graphIndex f) =
      insertion (graphIndex f) * graphMatrix A κ := by
  have hz (p : P) (i : D) : zeroExtend f A p (f i) = (insertion f * A) p i := by
    simp [zeroExtend, Matrix.mul_apply, Matrix.conjTranspose_apply, insertion,
      basisInsertion, f.injective.eq_iff]
  ext ⟨g,p⟩ ⟨h,i⟩
  fin_cases g <;> fin_cases h <;>
    simp [Matrix.mul_apply, insertion, basisInsertion, graphIndex, graphMatrix,
      Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.one_apply, hz, ite_and,
      Finset.mul_sum, ← Finset.sum_mul] <;> split_ifs <;> simp

/-- Adjoint intertwining holds for Hermitian input, for the actual full graph. -/
theorem graph_adjoint_intertwines (f : D ↪ P) (A : Matrix D D ℂ)
    (hA : A.IsHermitian) (κ : ℝ) :
    (insertion (graphIndex f))ᴴ * graphMatrix (zeroExtend f A) κ =
      graphMatrix A κ * (insertion (graphIndex f))ᴴ := by
  have h := congrArg Matrix.conjTranspose (graph_intertwines f A κ)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    show (graphMatrix A κ)ᴴ = graphMatrix A κ from graphMatrix_hermitian A hA κ,
    show (graphMatrix (zeroExtend f A) κ)ᴴ = graphMatrix (zeroExtend f A) κ from
      graphMatrix_hermitian _ (zeroExtend_hermitian f A hA) κ] at h
  exact h

@[simp] theorem graph_apply (f : D ↪ P) (A : Matrix D D ℂ) (κ : ℝ)
    (x : EuclideanSpace ℂ (Fin 4 × D)) :
    Matrix.toEuclideanCLM (n := Fin 4 × P) (𝕜 := ℂ) (graphMatrix (zeroExtend f A) κ)
      (graphIsometry f x) =
      graphIsometry f (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (graphMatrix A κ) x) :=
  matrix_intertwining_apply (graphIndex f) _ _ (graph_intertwines f A κ) x

@[simp] theorem graph_restrict (f : D ↪ P) (A : Matrix D D ℂ) (hA : A.IsHermitian) (κ : ℝ)
    (y : EuclideanSpace ℂ (Fin 4 × P)) :
    graphRestriction f (Matrix.toEuclideanCLM (n := Fin 4 × P) (𝕜 := ℂ)
      (graphMatrix (zeroExtend f A) κ) y) =
      Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (graphMatrix A κ) (graphRestriction f y) :=
  matrix_restriction_apply (graphIndex f) _ _ (graph_adjoint_intertwines f A hA κ) y

theorem graph_kernel_projection (f : D ↪ P) (A : Matrix D D ℂ) (hA : A.IsHermitian)
    (κ : ℝ) (x : EuclideanSpace ℂ (Fin 4 × D)) :
    Matrix.toEuclideanCLM (n := Fin 4 × P) (𝕜 := ℂ)
        (matrixKernelProjection (graphMatrix (zeroExtend f A) κ)) (graphIsometry f x) =
      graphIsometry f (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ)
        (matrixKernelProjection (graphMatrix A κ)) x) := by
  simp only [matrixKernelProjection, StarAlgEquiv.apply_symm_apply]
  exact reducing_kernel_projection (graphIsometry f) (graphRestriction f) _ _
    (coordinateIsometry_inner (graphIndex f)) (graph_apply f A κ) (graph_restrict f A hA κ) x

theorem graph_pseudoInverse (f : D ↪ P) (A : Matrix D D ℂ) (hA : A.IsHermitian)
    (κ : ℝ) (x : EuclideanSpace ℂ (Fin 4 × D)) :
    Matrix.toEuclideanCLM (n := Fin 4 × P) (𝕜 := ℂ)
        (matrixPseudoInverse (graphMatrix (zeroExtend f A) κ)
          (graphMatrix_hermitian _ (zeroExtend_hermitian f A hA) κ)) (graphIsometry f x) =
      graphIsometry f (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ)
        (matrixPseudoInverse (graphMatrix A κ) (graphMatrix_hermitian A hA κ)) x) := by
  simp only [matrixPseudoInverse, StarAlgEquiv.apply_symm_apply]
  exact reducing_pseudoInverse (graphIsometry f) (graphRestriction f) _ _
    (coordinateIsometry_inner (graphIndex f)) (graph_apply f A κ) (graph_restrict f A hA κ) _ _ x

theorem graph_polynomial (f : D ↪ P) (A : Matrix D D ℂ) (κ : ℝ) (p : ℝ[X])
    (x : EuclideanSpace ℂ (Fin 4 × D)) :
    polynomialOperator p (Matrix.toEuclideanCLM (n := Fin 4 × P) (𝕜 := ℂ)
      (graphMatrix (zeroExtend f A) κ)) (graphIsometry f x) =
      graphIsometry f (polynomialOperator p (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ)
        (graphMatrix A κ)) x) :=
  intertwining_polynomialOperator (graphIsometry f) _ _ (graph_apply f A κ) p x

@[simp] theorem graphInput_isometry (f : D ↪ P) (b : EuclideanSpace ℂ D) :
    graphInput (coordinateIsometry f b) = graphIsometry f (graphInput b) := by
  ext ⟨g,p⟩
  by_cases hg : g = 1 <;> simp [hg, graphInput, coordinateIsometry_apply, Matrix.mulVec, dotProduct,
    insertion, basisInsertion, graphIndex, Fintype.sum_prod_type, ite_and]

/-- Every graph Krylov vector is supported on the actual active data coordinates. -/
theorem graphKrylov_active (f : D ↪ P) (A : Matrix D D ℂ) (κ : ℝ) (b : EuclideanSpace ℂ D) :
    hermitianKrylov (Matrix.toEuclideanCLM (n := Fin 4 × P) (𝕜 := ℂ)
      (graphMatrix (zeroExtend f A) κ)) (graphInput (coordinateIsometry f b)) ≤
      LinearMap.range ((graphIsometry f).toLinearMap.restrictScalars ℝ) := by
  rw [graphInput_isometry]
  exact hermitianKrylov_le_range (graphIsometry f) _ _ (graph_apply f A κ) (graphInput b)

/-- The physical graph receives all projection and MP estimates directly from
the invertible logical matrix; there is no inverse of its singular zero extension. -/
theorem physical_graphInput_promises (f : D ↪ P) (A : Matrix D D ℂ) (hA : A.IsHermitian)
    (hunit : IsUnit (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A))
    {κ : ℝ} (hκ : 0 < κ)
    (hAnorm : ‖Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A‖ ≤ 1)
    (hinorm : ‖Ring.inverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A)‖ ≤ κ)
    (b : EuclideanSpace ℂ D) (hb : ‖b‖ = 1) :
    let s := ‖Ring.inverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) b‖
    let H := graphMatrix (zeroExtend f A) κ
    let e := graphInput (coordinateIsometry f b)
    let Q := (LinearMap.ker (Matrix.toEuclideanCLM (n := Fin 4 × P) (𝕜 := ℂ) H).toLinearMap).starProjection
    ‖e‖=1 ∧ s^2/(2*κ^2)≤‖Q e‖^2 ∧ ‖Q e‖^2≤s^2/κ^2 ∧
      0<‖Q e‖^2 ∧ ‖Q e‖^2≤1/2 ∧
      ‖Matrix.toEuclideanCLM (n := Fin 4 × P) (𝕜 := ℂ)
        (matrixPseudoInverse H (graphMatrix_hermitian _ (zeroExtend_hermitian f A hA) κ)) e‖≤s := by
  have h := graphInput_promises A hA hunit hκ hAnorm hinorm b hb
  dsimp only at h ⊢
  have hk := graph_kernel_projection f A hA κ (graphInput b)
  simp only [matrixKernelProjection, StarAlgEquiv.apply_symm_apply] at hk
  rw [graphInput_isometry, hk, graph_pseudoInverse f A hA,
    (graphIsometry f).norm_map, (graphIsometry f).norm_map, (graphIsometry f).norm_map]
  exact h

end OptimalQLS.PhysicalPadding
