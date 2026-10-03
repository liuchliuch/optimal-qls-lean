import OptimalQLS.LowerBounds.Theorem61
import OptimalQLS.PhysicalPadding.Complete
import OptimalQLS.PhysicalPadding.Dimensions

/-! Concrete computational padding of the lower-bound family. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
set_option linter.unusedSectionVars false
namespace OptimalQLS.LowerBounds.Physical
open Matrix PhysicalPadding
attribute [local instance] Classical.propDecidable
variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

abbrev Inactive (f : D ↪ P) := {p : P // p ∉ Set.range f}

def paddingCoordinates (f : D ↪ P) : D ⊕ Inactive f ≃ P :=
  (Equiv.sumCongr (Equiv.ofInjective f f.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range f))

@[simp] theorem paddingCoordinates_active (f : D ↪ P) (i : D) :
    paddingCoordinates f (.inl i) = f i := rfl

@[simp] theorem paddingCoordinates_inactive (f : D ↪ P) (i : Inactive f) :
    paddingCoordinates f (.inr i) = i.val := rfl

@[simp] theorem paddingCoordinates_symm_active (f : D ↪ P) (i : D) :
    (paddingCoordinates f).symm (f i) = .inl i := by
  apply (paddingCoordinates f).injective
  simp

@[simp] theorem paddingCoordinates_symm_inactive (f : D ↪ P) (i : Inactive f) :
    (paddingCoordinates f).symm i.val = .inr i := by
  apply (paddingCoordinates f).injective
  simp

/-- A chosen full unitary completion, identity on all inactive coordinates. -/
def extendUnitary (f : D ↪ P) (U : Matrix.unitaryGroup D ℂ) : Matrix.unitaryGroup P ℂ :=
  OptimalQLS.rewireUnitary (paddingCoordinates f) (blockSumUnitary U 1)

/-- Zero insertion at the level of the literal program's output amplitudes. -/
def insertVector (f : D ↪ P) (x : D → ℂ) : P → ℂ := insertion f *ᵥ x

@[simp] theorem insertVector_active (f : D ↪ P) (x : D → ℂ) (i : D) :
    insertVector f x (f i) = x i := insertion_mulVec_active f x i

@[simp] theorem insertVector_inactive (f : D ↪ P) (x : D → ℂ) (i : Inactive f) :
    insertVector f x i.val = 0 := insertion_mulVec_inactive f x i.val i.property

theorem insertVector_norm (f : D ↪ P) (x : D → ℂ) :
    ‖WithLp.toLp 2 (insertVector f x)‖ = ‖WithLp.toLp 2 x‖ :=
  (coordinateIsometry f).norm_map _

/-- Extracting the active output is exactly the adjoint inclusion. -/
theorem extract_insertVector (f : D ↪ P) (x : D → ℂ) :
    (insertion f)ᴴ *ᵥ insertVector f x = x := by
  rw [insertVector, Matrix.mulVec_mulVec, insertion_adjoint_mul, Matrix.one_mulVec]

theorem extendUnitary_entries (f : D ↪ P) (U : Matrix.unitaryGroup D ℂ)
    (i j : D ⊕ Inactive f) :
    extendUnitary f U (paddingCoordinates f i) (paddingCoordinates f j) =
      Matrix.fromBlocks (U : Matrix D D ℂ) 0 0 (1 : Matrix (Inactive f) (Inactive f) ℂ) i j := by
  simp [extendUnitary, OptimalQLS.rewireUnitary, blockSumUnitary]

@[simp] theorem zeroExtend_in_coordinates (f : D ↪ P) (A : Matrix D D ℂ)
    (i j : D ⊕ Inactive f) :
    zeroExtend f A (paddingCoordinates f i) (paddingCoordinates f j) =
      Matrix.fromBlocks A 0 0 (0 : Matrix (Inactive f) (Inactive f) ℂ) i j := by
  cases i with
  | inl i =>
    cases j with
    | inl j => exact zeroExtend_active_entries f A i j
    | inr j => exact zeroExtend_inactive_column f A (f i) j.val j.property
  | inr i =>
    cases j <;> exact zeroExtend_inactive_row f A i.val _ i.property

theorem extendUnitary_sub (f : D ↪ P) (U V : Matrix.unitaryGroup D ℂ) :
    (extendUnitary f U : Matrix P P ℂ) - (extendUnitary f V : Matrix P P ℂ) =
      zeroExtend f ((U : Matrix D D ℂ) - (V : Matrix D D ℂ)) := by
  ext i j
  obtain ⟨i, rfl⟩ := (paddingCoordinates f).surjective i
  obtain ⟨j, rfl⟩ := (paddingCoordinates f).surjective j
  simp only [Matrix.sub_apply, extendUnitary_entries, zeroExtend_in_coordinates]
  cases i <;> cases j <;> simp

theorem extendUnitary_distance (f : D ↪ P) [Nonempty D] (U V : Matrix.unitaryGroup D ℂ) :
    ‖(extendUnitary f U : Matrix P P ℂ) - (extendUnitary f V : Matrix P P ℂ)‖ =
      ‖(U : Matrix D D ℂ) - (V : Matrix D D ℂ)‖ := by
  rw [extendUnitary_sub, zeroExtend_norm]

theorem extendUnitary_prepares (f : D ↪ P) (U : Matrix.unitaryGroup D ℂ)
    (i₀ : D) (x : D → ℂ) (h : ∀ i, U i i₀ = x i) (p : P) :
    extendUnitary f U p (f i₀) = insertVector f x p := by
  obtain ⟨p, rfl⟩ := (paddingCoordinates f).surjective p
  rw [← paddingCoordinates_active f i₀, extendUnitary_entries]
  cases p with
  | inl i => simpa using h i
  | inr i => simp

@[simp] theorem zeroExtend_trace (f : D ↪ P) (A : Matrix D D ℂ) :
    (zeroExtend f A).trace = A.trace := by
  rw [zeroExtend, Matrix.trace_mul_cycle, insertion_adjoint_mul, Matrix.one_mul]

theorem zeroExtend_expectation (f : D ↪ P) (A B : Matrix D D ℂ) :
    (zeroExtend f A * zeroExtend f B).trace = (A * B).trace := by
  rw [← zeroExtend_mul, zeroExtend_trace]

@[simp] theorem insertVector_pureDensity (f : D ↪ P) (x : D → ℂ) :
    pureDensity (insertVector f x) = zeroExtend f (pureDensity x) :=
  pureDensity_mulVec (insertion f) x

@[simp] theorem insertVector_ketBra (f : D ↪ P) (x : D → ℂ) :
    ketBra (insertVector f x) (insertVector f x) = zeroExtend f (ketBra x x) :=
  insertVector_pureDensity f x

/-- A diagonal observable is extended by zero on unused physical outputs. -/
def insertWeight (f : D ↪ P) (w : D → ℝ) : P → ℝ :=
  fun p => Sum.elim w (fun _ => 0) ((paddingCoordinates f).symm p)

@[simp] theorem insertWeight_active (f : D ↪ P) (w : D → ℝ) (i : D) :
    insertWeight f w (f i) = w i := by simp [insertWeight]

@[simp] theorem insertWeight_inactive (f : D ↪ P) (w : D → ℝ) (i : Inactive f) :
    insertWeight f w i.val = 0 := by simp [insertWeight]

theorem insertWeight_bound (f : D ↪ P) (w : D → ℝ) (h : ∀ i, |w i| ≤ 1) :
    ∀ p, |insertWeight f w p| ≤ 1 := by
  intro p
  obtain ⟨p, rfl⟩ := (paddingCoordinates f).surjective p
  cases p with
  | inl p => simpa using h p
  | inr p => simp

theorem insertWeight_diagonal (f : D ↪ P) (w : D → ℝ) :
    Matrix.diagonal (fun p => (insertWeight f w p : ℂ)) =
      zeroExtend f (Matrix.diagonal (fun i => (w i : ℂ))) := by
  ext i j
  obtain ⟨i, rfl⟩ := (paddingCoordinates f).surjective i
  obtain ⟨j, rfl⟩ := (paddingCoordinates f).surjective j
  rw [zeroExtend_in_coordinates]
  simp only [Matrix.diagonal_apply, (paddingCoordinates f).injective.eq_iff]
  cases i <;> cases j <;> simp [Matrix.diagonal_apply]

end OptimalQLS.LowerBounds.Physical
