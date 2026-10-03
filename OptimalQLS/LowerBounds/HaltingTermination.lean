import OptimalQLS.LowerBounds.HaltingInstrument

/-! Actual abort and query-free completion channels for a halting protocol. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
variable {D A : Type*} [Fintype D] [DecidableEq D] [Fintype A] [DecidableEq A]

def basisRow (a : A) : Matrix Unit A ℂ := fun _ j => if j = a then 1 else 0

theorem basisRow_gram_sum : (∑ a : A, (basisRow a).conjTranspose * basisRow a) = (1 : Matrix A A ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, basisRow, Matrix.one_apply]
  · simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, basisRow,
      Matrix.one_apply, hij, Ne.symm hij, ite_mul, mul_ite]

theorem basisRow_conjugation (X : Matrix A A ℂ) (a : A) :
    basisRow a * X * (basisRow a).conjTranspose = fun _ _ : Unit => X a a := by
  ext i j
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, basisRow]

theorem basisRow_conjugation_sum (X : Matrix A A ℂ) :
    (∑ a : A, basisRow a * X * (basisRow a).conjTranspose) = X.trace • (1 : Matrix Unit Unit ℂ) := by
  simp only [basisRow_conjugation]
  ext i j
  simp [Matrix.sum_apply, Matrix.trace, Matrix.smul_apply]

def abortKraus : Unit ⊕ A → Matrix (D ⊕ Unit) (D ⊕ A) ℂ
  | .inl _ => Matrix.fromBlocks 1 0 0 0
  | .inr a => Matrix.fromBlocks 0 0 0 (basisRow a)

theorem abortKraus_normalized : (∑ i : Unit ⊕ A,
    (abortKraus (D := D) i).conjTranspose * abortKraus i) = 1 := by
  simp only [Fintype.sum_sum_type, Fintype.sum_unique, abortKraus,
    Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    zero_add, add_zero]
  rw [sum_fromBlocks]
  simp only [Finset.sum_const_zero, basisRow_gram_sum, Matrix.fromBlocks_add, add_zero, zero_add]
  exact Matrix.fromBlocks_one

/-- Preserve completed output and move every live basis outcome into a separate abort flag. -/
def abortChannel : FiniteChannel (D ⊕ A) (D ⊕ Unit) :=
  FiniteChannel.ofKraus abortKraus abortKraus_normalized

theorem abortChannel_apply (Y : Matrix D D ℂ) (X : Matrix A A ℂ) :
    (abortChannel (D := D) (A := A)).apply (Matrix.fromBlocks Y 0 0 X) =
      Matrix.fromBlocks Y 0 0 (X.trace • (1 : Matrix Unit Unit ℂ)) := by
  rw [abortChannel, FiniteChannel.ofKraus_apply]
  simp only [Fintype.sum_sum_type, Fintype.sum_unique, abortKraus,
    Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    zero_add, add_zero]
  rw [sum_fromBlocks]
  simp only [Finset.sum_const_zero, basisRow_conjugation_sum, Matrix.fromBlocks_add, add_zero, zero_add]

def finishKraus (F : FiniteChannel A D) : Unit ⊕ Fin F.rank → Matrix (D ⊕ Unit) (D ⊕ A) ℂ
  | .inl _ => Matrix.fromBlocks 1 0 0 0
  | .inr i => Matrix.fromBlocks 0 (F.kraus i) 0 0

theorem finishKraus_normalized (F : FiniteChannel A D) :
    (∑ i, (finishKraus F i).conjTranspose * finishKraus F i) = 1 := by
  simp only [Fintype.sum_sum_type, Fintype.sum_unique, finishKraus,
    Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    zero_add, add_zero]
  rw [sum_fromBlocks]
  simp only [Finset.sum_const_zero, F.normalized, Matrix.fromBlocks_add, add_zero, zero_add]
  exact Matrix.fromBlocks_one

/-- A query-free final channel converts any remaining live state to ordinary
completed output; its abort component is identically zero. -/
def finishChannel (F : FiniteChannel A D) : FiniteChannel (D ⊕ A) (D ⊕ Unit) :=
  FiniteChannel.ofKraus (finishKraus F) (finishKraus_normalized F)

theorem finishChannel_apply (F : FiniteChannel A D) (Y : Matrix D D ℂ) (X : Matrix A A ℂ) :
    (finishChannel F).apply (Matrix.fromBlocks Y 0 0 X) =
      Matrix.fromBlocks (Y + F.apply X) 0 0 (0 : Matrix Unit Unit ℂ) := by
  rw [finishChannel, FiniteChannel.ofKraus_apply]
  simp only [Fintype.sum_sum_type, Fintype.sum_unique, finishKraus,
    Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    zero_add, add_zero]
  rw [sum_fromBlocks]
  simp only [Finset.sum_const_zero, Matrix.fromBlocks_add, add_zero, zero_add]
  rfl

def abortProjection : Matrix (D ⊕ Unit) (D ⊕ Unit) ℂ := Matrix.fromBlocks 0 0 0 1

theorem abortProjection_norm_le_one : ‖abortProjection (D := D)‖ ≤ 1 := by
  simp [abortProjection, blockDiagonal_norm]

theorem abortProjection_probability (Y : Matrix D D ℂ) (X : Matrix A A ℂ) :
    (abortProjection * (abortChannel (D := D) (A := A)).apply (Matrix.fromBlocks Y 0 0 X)).trace.re = X.trace.re := by
  rw [abortChannel_apply, abortProjection, Matrix.fromBlocks_multiply]
  simp [trace_blockDiagonal]

@[simp] theorem abortProjection_no_abort (Y : Matrix D D ℂ) :
    (abortProjection * Matrix.fromBlocks Y 0 0 (0 : Matrix Unit Unit ℂ)).trace.re = 0 := by
  rw [abortProjection, Matrix.fromBlocks_multiply]
  simp

/-- A genuine continuation residual of trace equal to the live block can replace
the abort branch at trace-distance cost at most that live probability. -/
theorem completed_vs_abort_distance (Y R : Matrix D D ℂ) (X : Matrix A A ℂ)
    (hX : X.PosSemidef) (hR : R.PosSemidef) (htrace : R.trace.re = X.trace.re) :
    traceDistance (Matrix.fromBlocks (Y + R) 0 0 (0 : Matrix Unit Unit ℂ))
      ((abortChannel (D := D) (A := A)).apply (Matrix.fromBlocks Y 0 0 X)) ≤ X.trace.re := by
  let G : Matrix (D ⊕ Unit) (D ⊕ Unit) ℂ := Matrix.fromBlocks Y 0 0 0
  let S : Matrix (D ⊕ Unit) (D ⊕ Unit) ℂ := Matrix.fromBlocks R 0 0 0
  let T : Matrix (D ⊕ Unit) (D ⊕ Unit) ℂ :=
    (abortChannel (D := D) (A := A)).apply (Matrix.fromBlocks 0 0 0 X)
  have hS : S.PosSemidef := blockDiagonal_positive hR Matrix.PosSemidef.zero
  have hT : T.PosSemidef := (abortChannel (D := D) (A := A)).apply_positive
    (blockDiagonal_positive Matrix.PosSemidef.zero hX)
  have hSt : S.trace.re = X.trace.re := by simpa [S, trace_blockDiagonal] using htrace
  have hTt : T.trace.re = X.trace.re := by
    dsimp only [T]
    rw [FiniteChannel.trace_apply, trace_blockDiagonal]
    simp
  have h := traceDistance_common_positive_residual G S T hS hT X.trace.re hSt hTt
  simpa [G, S, T, abortChannel_apply, Matrix.fromBlocks_add] using h

end OptimalQLS.LowerBounds
