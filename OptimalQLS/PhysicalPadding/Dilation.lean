import OptimalQLS.PhysicalPadding.Operators
import OptimalQLS.PhysicalPadding.Registers
import OptimalQLS.LowerBounds.HermitianDilation

/-! Zero-padding commutes with the literal one-data-qubit Hermitian dilation.
The whole supplied matrix oracle is still the existing dilationEncoding UA. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace OptimalQLS.PhysicalPadding
open Matrix PolynomialTransform LowerBounds
open scoped BigOperators Matrix.Norms.L2Operator
variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

def sumIndex (f : D ↪ P) : (D ⊕ D) ↪ (P ⊕ P) := f.sumMap f

@[simp] theorem sumIndex_inl (f : D ↪ P) (i : D) : sumIndex f (.inl i) = .inl (f i) := rfl
@[simp] theorem sumIndex_inr (f : D ↪ P) (i : D) : sumIndex f (.inr i) = .inr (f i) := rfl

theorem insertion_sumIndex (f : D ↪ P) :
    insertion (sumIndex f) = Matrix.fromBlocks (insertion f) 0 0 (insertion f) := by
  ext p i
  cases p <;> cases i <;> simp [insertion, basisInsertion, sumIndex]

/-- The physical dilation is the full zero extension of the logical dilation. -/
theorem zeroExtend_hermitianDilation (f : D ↪ P) (A : Matrix D D ℂ) :
    zeroExtend (sumIndex f) (hermitianDilation A) = hermitianDilation (zeroExtend f A) := by
  simp only [zeroExtend, insertion_sumIndex, hermitianDilation, Matrix.fromBlocks_conjTranspose,
    Matrix.conjTranspose_zero, Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
    zero_add, add_zero, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  congr 1
  exact Matrix.mul_assoc ..

/-- Left-half source embedding preserves all physical unused zero amplitudes. -/
theorem sumIndex_source_left (f : D ↪ P) (b : EuclideanSpace ℂ D) :
    coordinateIsometry (sumIndex f) (WithLp.toLp 2 (Sum.elim (WithLp.ofLp b) 0)) =
      WithLp.toLp 2 (Sum.elim (WithLp.ofLp (coordinateIsometry f b)) 0) := by
  change WithLp.toLp 2 (insertion (sumIndex f) *ᵥ Sum.elim (WithLp.ofLp b) 0) = _
  rw [insertion_sumIndex, Matrix.fromBlocks_mulVec]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec,
    Matrix.mulVec_zero, add_zero, zero_add]
  rfl

/-- Right-half solution extraction has the same literal physical insertion. -/
theorem sumIndex_source_right (f : D ↪ P) (b : EuclideanSpace ℂ D) :
    coordinateIsometry (sumIndex f) (WithLp.toLp 2 (Sum.elim (0 : D → ℂ) (WithLp.ofLp b))) =
      WithLp.toLp 2 (Sum.elim (0 : P → ℂ) (WithLp.ofLp (coordinateIsometry f b))) := by
  change WithLp.toLp 2 (insertion (sumIndex f) *ᵥ Sum.elim (0 : D → ℂ) (WithLp.ofLp b)) = _
  rw [insertion_sumIndex, Matrix.fromBlocks_mulVec]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec,
    Matrix.mulVec_zero, add_zero, zero_add]
  rfl

/-- The extra dilation label is one literal two-valued data bit. -/
def sumDataCoordinates (P : Type*) : (P ⊕ P) ≃ Bool × P where
  toFun p := match p with | .inl i => (false,i) | .inr i => (true,i)
  invFun p := if p.1 then .inr p.2 else .inl p.2
  left_inv p := by cases p <;> rfl
  right_inv p := by rcases p with ⟨b,i⟩; cases b <;> rfl

@[simp] theorem sumDataCoordinates_zero {d : ℕ} :
    sumDataCoordinates (Fin (physicalDimension d)) (.inl 0) = (false,0) := rfl

@[simp] theorem sumIndex_active_zero {d : ℕ} [NeZero d] :
    sumIndex (activeIndex d) (.inl 0) = .inl 0 := rfl

theorem physical_dilation_cardinality (d : ℕ) :
    Fintype.card (Fin (physicalDimension d) ⊕ Fin (physicalDimension d)) =
      2^(dataQubits d+1) := by
  simp [physicalDimension, pow_succ, mul_two]

end OptimalQLS.PhysicalPadding
