import OptimalQLS.GraphEncoding.Construction
import OptimalQLS.MatrixPseudoInverse

/-! # Isometric transport from the active three-sector geometry to physical two qubits -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
namespace OptimalQLS.GraphEncoding
open Matrix Geometry
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Actual zero-padding of the fourth physical graph label. -/
def activeTriple : Block (EuclideanSpace ℂ D) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 4 × D) where
  toFun x := WithLp.toLp 2 (fun gd => ![x 0 gd.2, x 1 gd.2, x 2 gd.2, 0] gd.1)
  map_add' x y := by ext ⟨g,d⟩; fin_cases g <;> simp
  map_smul' c x := by ext ⟨g,d⟩; fin_cases g <;> simp
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, PiLp.norm_sq_eq_of_L2]
    change (∑ gd : Fin 4 × D, ‖![x 0 gd.2, x 1 gd.2, x 2 gd.2, (0 : ℂ)] gd.1‖^2) = ∑ g : Fin 3, ‖x g‖^2
    simp [Fintype.sum_prod_type, Fin.sum_univ_succ, EuclideanSpace.norm_sq_eq]


@[simp] theorem activeTriple_zero (x : Block (EuclideanSpace ℂ D)) (d : D) :
    activeTriple x (0,d) = x 0 d := rfl
@[simp] theorem activeTriple_one (x : Block (EuclideanSpace ℂ D)) (d : D) :
    activeTriple x (1,d) = x 1 d := rfl
@[simp] theorem activeTriple_two (x : Block (EuclideanSpace ℂ D)) (d : D) :
    activeTriple x (2,d) = x 2 d := rfl
@[simp] theorem activeTriple_three (x : Block (EuclideanSpace ℂ D)) (d : D) :
    activeTriple x (3,d) = 0 := rfl

/-- Restriction to active graph labels, the actual adjoint of zero-padding. -/
def activeRestriction : EuclideanSpace ℂ (Fin 4 × D) →L[ℂ] Block (EuclideanSpace ℂ D) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 ![WithLp.toLp 2 (fun d => x (0,d)),
        WithLp.toLp 2 (fun d => x (1,d)), WithLp.toLp 2 (fun d => x (2,d))]
      map_add' := by intros; ext g d; fin_cases g <;> rfl
      map_smul' := by intros; ext g d; fin_cases g <;> rfl }

@[simp] theorem activeRestriction_activeTriple (x : Block (EuclideanSpace ℂ D)) :
    activeRestriction (activeTriple x) = x := by ext g d; fin_cases g <;> rfl

theorem activeTriple_inner (x : Block (EuclideanSpace ℂ D)) (y : EuclideanSpace ℂ (Fin 4 × D)) :
    inner ℂ (activeTriple x) y = inner ℂ x (activeRestriction y) := by
  simp [PiLp.inner_apply, Fintype.sum_prod_type, Fin.sum_univ_succ,
    activeTriple, activeRestriction]


/-- The padded physical matrix intertwines with the original auxiliary operator. -/
theorem activeTriple_intertwines (A : Matrix D D ℂ) (κ : ℝ)
    (x : Block (EuclideanSpace ℂ D)) :
    Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (graphMatrix A κ) (activeTriple x) =
      activeTriple (blockAuxiliary (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) κ⁻¹ x) := by
  ext ⟨g,d⟩
  fin_cases g <;>
    simp [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, graphMatrix,
      Fintype.sum_prod_type, Fin.sum_univ_succ, activeTriple, blockAuxiliary,
      Matrix.one_apply, mul_sub, Finset.sum_sub_distrib, sub_eq_add_neg]

theorem activeRestriction_intertwines (A : Matrix D D ℂ) (κ : ℝ)
    (x : EuclideanSpace ℂ (Fin 4 × D)) :
    activeRestriction (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (graphMatrix A κ) x) =
      blockAuxiliary (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) κ⁻¹ (activeRestriction x) := by
  ext g d
  fin_cases g <;>
    simp [activeRestriction, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, graphMatrix,
      Fintype.sum_prod_type, Fin.sum_univ_succ, blockAuxiliary,
      Matrix.one_apply, mul_sub, Finset.sum_sub_distrib, sub_eq_add_neg]

theorem graphMatrix_hermitian (A : Matrix D D ℂ) (hA : A.IsHermitian) (κ : ℝ) :
    (graphMatrix A κ).IsHermitian := by
  ext ⟨g,i⟩ ⟨h,j⟩
  have ha (i j : D) : star (A j i) = A i j := congrFun (congrFun hA i) j
  fin_cases g <;> fin_cases h <;>
    simp [Matrix.conjTranspose_apply, graphMatrix, ha, Matrix.one_apply, eq_comm] <;>
    split_ifs <;> simp

/-- Zero-padding commutes with the exact orthogonal projection onto the actual kernel. -/
theorem activeTriple_kernel_projection (A : Matrix D D ℂ) (κ : ℝ)
    (x : Block (EuclideanSpace ℂ D)) :
    (LinearMap.ker (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (graphMatrix A κ)).toLinearMap).starProjection
      (activeTriple x) =
    activeTriple ((LinearMap.ker
      (blockAuxiliary (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) κ⁻¹).toLinearMap).starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · change Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (graphMatrix A κ) (activeTriple _) = 0
    rw [activeTriple_intertwines]
    have hh := (LinearMap.ker (blockAuxiliary (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) κ⁻¹).toLinearMap).starProjection_apply_mem x
    change blockAuxiliary (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) κ⁻¹ _ = 0 at hh
    rw [hh, map_zero]
  · intro w hw
    have hw' : activeRestriction w ∈ LinearMap.ker
        (blockAuxiliary (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) κ⁻¹).toLinearMap := by
      change blockAuxiliary (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) κ⁻¹ (activeRestriction w) = 0
      rw [← activeRestriction_intertwines]
      change Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (graphMatrix A κ) w = 0 at hw
      rw [hw, map_zero]
    rw [← map_sub, activeTriple_inner]
    exact (LinearMap.ker (blockAuxiliary (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) κ⁻¹).toLinearMap).starProjection_inner_eq_zero x _ hw'

/-- Matrix-level version usable directly by the physical kernel reflection. -/
theorem activeTriple_matrix_kernel (A : Matrix D D ℂ) (κ : ℝ)
    (x : Block (EuclideanSpace ℂ D)) :
    Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (matrixKernelProjection (graphMatrix A κ)) (activeTriple x) =
      activeTriple ((LinearMap.ker
        (blockAuxiliary (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) κ⁻¹).toLinearMap).starProjection x) := by
  rw [matrixKernelProjection, StarAlgEquiv.apply_symm_apply]
  exact activeTriple_kernel_projection A κ x


/-- The genuine spectral inverse has image orthogonal to the actual kernel. -/
theorem pseudoInverse_inner_kernel {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (H : E →L[ℂ] E) (hH : H.toLinearMap.IsSymmetric) (x w : E)
    (hw : w ∈ LinearMap.ker H.toLinearMap) :
    inner ℂ (hermitianPseudoInverse H hH x) w = 0 := by
  have hfix := (LinearMap.ker H.toLinearMap).starProjection_eq_self_iff.mpr hw
  have hz := congrArg (fun T : E →L[ℂ] E => T w) (hermitianPseudoInverse_mul_kernel H hH)
  change hermitianPseudoInverse H hH ((LinearMap.ker H.toLinearMap).starProjection w) = 0 at hz
  rw [hfix] at hz
  have hs := (hermitianPseudoInverse_symmetric H hH) x w
  change inner ℂ (hermitianPseudoInverse H hH x) w = inner ℂ x (hermitianPseudoInverse H hH w) at hs
  rw [hs, hz]
  simp

/-- Moore–Penrose transport follows from kernel transport and the canonical
spectral inverse's range, rather than a supplied inverse certificate. -/
theorem activeTriple_pseudoInverse (A : Matrix D D ℂ) (hA : A.IsHermitian) (κ : ℝ)
    (x : Block (EuclideanSpace ℂ D)) :
    hermitianPseudoInverse
      (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (graphMatrix A κ))
      (matrixHermitian_symmetric _ (graphMatrix_hermitian A hA κ)) (activeTriple x) =
      activeTriple (hermitianPseudoInverse
        (blockAuxiliary (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) κ⁻¹)
        (lemma42_auxiliary_hermitian _ (matrixHermitian_symmetric A hA) κ⁻¹) x) := by
  let H := Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (graphMatrix A κ)
  let T := blockAuxiliary (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) κ⁻¹
  let hH := matrixHermitian_symmetric (graphMatrix A κ) (graphMatrix_hermitian A hA κ)
  let hT := lemma42_auxiliary_hermitian _ (matrixHermitian_symmetric A hA) κ⁻¹
  let y := hermitianPseudoInverse H hH (activeTriple x) -
    activeTriple (hermitianPseudoInverse T hT x)
  have hy : y ∈ LinearMap.ker H.toLinearMap := by
    have hp := congrArg (fun C : EuclideanSpace ℂ (Fin 4 × D) →L[ℂ] EuclideanSpace ℂ (Fin 4 × D) =>
      C (activeTriple x)) (hermitian_mul_pseudoInverse H hH)
    have ht := congrArg (fun C : Block (EuclideanSpace ℂ D) →L[ℂ] Block (EuclideanSpace ℂ D) =>
      C x) (hermitian_mul_pseudoInverse T hT)
    change H (hermitianPseudoInverse H hH (activeTriple x)) =
      activeTriple x - (LinearMap.ker H.toLinearMap).starProjection (activeTriple x) at hp
    change T (hermitianPseudoInverse T hT x) = x - (LinearMap.ker T.toLinearMap).starProjection x at ht
    change H (hermitianPseudoInverse H hH (activeTriple x) -
      activeTriple (hermitianPseudoInverse T hT x)) = 0
    rw [map_sub, hp]
    change activeTriple x - (LinearMap.ker H.toLinearMap).starProjection (activeTriple x) -
      Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (graphMatrix A κ)
        (activeTriple (hermitianPseudoInverse T hT x)) = 0
    rw [activeTriple_intertwines]
    change activeTriple x - (LinearMap.ker H.toLinearMap).starProjection (activeTriple x) -
      activeTriple (T (hermitianPseudoInverse T hT x)) = 0
    rw [ht, map_sub]
    change activeTriple x - (LinearMap.ker
      (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (graphMatrix A κ)).toLinearMap).starProjection
      (activeTriple x) - (activeTriple x - activeTriple ((LinearMap.ker T.toLinearMap).starProjection x)) = 0
    rw [activeTriple_kernel_projection]
    simp [T]
  have hrest : activeRestriction y ∈ LinearMap.ker T.toLinearMap := by
    change T (activeRestriction y) = 0
    change Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (graphMatrix A κ) y = 0 at hy
    change blockAuxiliary (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) κ⁻¹ (activeRestriction y) = 0
    rw [← activeRestriction_intertwines, hy, map_zero]
  have hi : inner ℂ y y = 0 := by
    change inner ℂ (hermitianPseudoInverse H hH (activeTriple x) -
      activeTriple (hermitianPseudoInverse T hT x)) y = 0
    rw [inner_sub_left, pseudoInverse_inner_kernel H hH _ _ hy,
      activeTriple_inner, pseudoInverse_inner_kernel T hT _ _ hrest]
    simp
  exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℂ)).mp hi)

/-- The existing original-coordinate auxiliary pseudoinverse agrees with the
actual padded physical matrix pseudoinverse on the entire active subspace. -/
theorem activeTriple_matrix_pseudoInverse (A : Matrix D D ℂ) (hA : A.IsHermitian)
    {κ : ℝ} (hκ : 0 < κ) (x : Block (EuclideanSpace ℂ D)) :
    Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ)
      (matrixPseudoInverse (graphMatrix A κ) (graphMatrix_hermitian A hA κ)) (activeTriple x) =
      activeTriple (auxiliaryPseudoInverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A)
        (matrixHermitian_symmetric A hA) κ⁻¹ x) := by
  rw [matrixPseudoInverse, StarAlgEquiv.apply_symm_apply, activeTriple_pseudoInverse A hA κ x,
    hermitianPseudoInverse_auxiliary_eq _ _ hκ]

end OptimalQLS.GraphEncoding
