import OptimalQLS.PhysicalPadding.Basis
import OptimalQLS.PhysicalPadding.ReducingTransport

/-! The reducing active data subspace of the singular, zero-extended matrix. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace OptimalQLS.PhysicalPadding
open Matrix Polynomial PolynomialTransform
open scoped BigOperators Matrix.Norms.L2Operator
variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

@[simp] theorem zeroExtend_add (f : D ↪ P) (A B : Matrix D D ℂ) :
    zeroExtend f (A+B) = zeroExtend f A + zeroExtend f B := by
  simp [zeroExtend, Matrix.mul_add, Matrix.add_mul]

@[simp] theorem zeroExtend_smul (f : D ↪ P) (c : ℂ) (A : Matrix D D ℂ) :
    zeroExtend f (c • A) = c • zeroExtend f A := by
  simp [zeroExtend, Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem zeroExtend_real_smul (f : D ↪ P) (c : ℝ) (A : Matrix D D ℂ) :
    zeroExtend f (c • A) = c • zeroExtend f A := by
  simp [zeroExtend, Matrix.mul_smul, Matrix.smul_mul]

/-- Padding respects composition, while the padded identity is only the active projection. -/
@[simp] theorem zeroExtend_mul (f : D ↪ P) (A B : Matrix D D ℂ) :
    zeroExtend f (A*B) = zeroExtend f A * zeroExtend f B := by
  simp only [zeroExtend, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (insertion f)ᴴ (insertion f), insertion_adjoint_mul,
    Matrix.one_mul]

@[simp] theorem zeroExtend_one (f : D ↪ P) :
    zeroExtend f (1 : Matrix D D ℂ) = insertion f * (insertion f)ᴴ := by
  simp [zeroExtend]

@[simp] theorem insertion_adjoint_mulVec (f : D ↪ P) (y : P → ℂ) (i : D) :
    ((insertion f)ᴴ *ᵥ y) i = y (f i) := by
  simp [insertion, basisInsertion, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]

@[simp] theorem zeroExtend_active_entries (f : D ↪ P) (A : Matrix D D ℂ) (i j : D) :
    zeroExtend f A (f i) (f j) = A i j := by
  simp [zeroExtend, insertion, basisInsertion, Matrix.mul_apply,
    Matrix.conjTranspose_apply, f.injective.eq_iff]

theorem zeroExtend_inactive_row (f : D ↪ P) (A : Matrix D D ℂ) (p q : P)
    (hp : p ∉ Set.range f) : zeroExtend f A p q = 0 := by
  have hh : ∀ i, p ≠ f i := by simpa [Set.mem_range, eq_comm] using hp
  simp [zeroExtend, insertion, basisInsertion, Matrix.mul_apply, hh]

theorem zeroExtend_inactive_column (f : D ↪ P) (A : Matrix D D ℂ) (p q : P)
    (hq : q ∉ Set.range f) : zeroExtend f A p q = 0 := by
  have hh : ∀ i, q ≠ f i := by simpa [Set.mem_range, eq_comm] using hq
  simp [zeroExtend, insertion, basisInsertion, Matrix.mul_apply, Matrix.conjTranspose_apply, hh]

/-- Matrix intertwining is the literal Hilbert-space action intertwining. -/
theorem matrix_intertwining_apply (f : D ↪ P) (H : Matrix P P ℂ) (T : Matrix D D ℂ)
    (h : H * insertion f = insertion f * T) (x : EuclideanSpace ℂ D) :
    Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) H (coordinateIsometry f x) =
      coordinateIsometry f (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) T x) := by
  change WithLp.toLp 2 (H *ᵥ (insertion f *ᵥ WithLp.ofLp x)) =
    WithLp.toLp 2 (insertion f *ᵥ (T *ᵥ WithLp.ofLp x))
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

theorem matrix_restriction_apply (f : D ↪ P) (H : Matrix P P ℂ) (T : Matrix D D ℂ)
    (h : (insertion f)ᴴ * H = T * (insertion f)ᴴ) (y : EuclideanSpace ℂ P) :
    restriction f (Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) H y) =
      Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) T (restriction f y) := by
  have hr (z : EuclideanSpace ℂ P) :
      restriction f z = WithLp.toLp 2 ((insertion f)ᴴ *ᵥ WithLp.ofLp z) := by
    ext i
    exact (insertion_adjoint_mulVec f _ i).symm
  rw [hr, hr y]
  change WithLp.toLp 2 ((insertion f)ᴴ *ᵥ (H *ᵥ WithLp.ofLp y)) =
    WithLp.toLp 2 (T *ᵥ ((insertion f)ᴴ *ᵥ WithLp.ofLp y))
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

@[simp] theorem zeroExtend_apply (f : D ↪ P) (A : Matrix D D ℂ) (x : EuclideanSpace ℂ D) :
    Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) (zeroExtend f A) (coordinateIsometry f x) =
      coordinateIsometry f (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A x) :=
  matrix_intertwining_apply f _ _ (zeroExtend_intertwines f A) x

@[simp] theorem zeroExtend_restrict (f : D ↪ P) (A : Matrix D D ℂ) (y : EuclideanSpace ℂ P) :
    restriction f (Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) (zeroExtend f A) y) =
      Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A (restriction f y) :=
  matrix_restriction_apply f _ _ (zeroExtend_adjoint_intertwines f A) y

theorem zeroExtend_kernel_projection (f : D ↪ P) (A : Matrix D D ℂ)
    (x : EuclideanSpace ℂ D) :
    Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) (matrixKernelProjection (zeroExtend f A))
        (coordinateIsometry f x) =
      coordinateIsometry f (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (matrixKernelProjection A) x) := by
  simp only [matrixKernelProjection, StarAlgEquiv.apply_symm_apply]
  exact reducing_kernel_projection (coordinateIsometry f) (restriction f) _ _
    (coordinateIsometry_inner f) (zeroExtend_apply f A) (zeroExtend_restrict f A) x

theorem zeroExtend_pseudoInverse (f : D ↪ P) (A : Matrix D D ℂ) (hA : A.IsHermitian)
    (x : EuclideanSpace ℂ D) :
    Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ)
        (matrixPseudoInverse (zeroExtend f A) (zeroExtend_hermitian f A hA))
        (coordinateIsometry f x) =
      coordinateIsometry f (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (matrixPseudoInverse A hA) x) := by
  simp only [matrixPseudoInverse, StarAlgEquiv.apply_symm_apply]
  exact reducing_pseudoInverse (coordinateIsometry f) (restriction f) _ _
    (coordinateIsometry_inner f) (zeroExtend_apply f A) (zeroExtend_restrict f A) _ _ x

theorem zeroExtend_polynomial (f : D ↪ P) (A : Matrix D D ℂ) (p : ℝ[X])
    (x : EuclideanSpace ℂ D) :
    polynomialOperator p (Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) (zeroExtend f A))
        (coordinateIsometry f x) =
      coordinateIsometry f (polynomialOperator p (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) x) :=
  intertwining_polynomialOperator (coordinateIsometry f) _ _ (zeroExtend_apply f A) p x

/-- The active inverse is defined without ever inverting the singular physical matrix. -/
def activeInverse (f : D ↪ P) (A : Matrix D D ℂ) : Matrix P P ℂ :=
  zeroExtend f (Ring.inverse A)

@[simp] theorem activeInverse_apply (f : D ↪ P) (A : Matrix D D ℂ) (b : EuclideanSpace ℂ D) :
    Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) (activeInverse f A) (coordinateIsometry f b) =
      coordinateIsometry f (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (Ring.inverse A) b) :=
  zeroExtend_apply f _ b

/-- The singular physical system is exactly solved on its reducing active subspace. -/
theorem activeInverse_solves (f : D ↪ P) (A : Matrix D D ℂ) (hA : IsUnit A)
    (b : EuclideanSpace ℂ D) :
    Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) (zeroExtend f A)
      (Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) (activeInverse f A) (coordinateIsometry f b)) =
      coordinateIsometry f b := by
  rw [activeInverse_apply, zeroExtend_apply, Perturbation.toEuclideanCLM_inverse A hA]
  exact congrArg (coordinateIsometry f) (Perturbation.apply_inverse
    (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A)
    (hA.map (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)).toMonoidHom) b)

end OptimalQLS.PhysicalPadding
