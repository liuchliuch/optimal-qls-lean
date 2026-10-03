import OptimalQLS.LowerBounds.QueryPortDistance
import OptimalQLS.LowerBounds.SumBlockEncoding

/-!
# Concrete exit/continue quantum instruments

Each live branch is routed by literal finite Kraus matrices either to a
completed output or back to live memory. Completeness is the ordinary
trace-preserving Kraus identity. The induced channel retains completed output
unchanged and decoheres the exit/continue choice by recording its Kraus label.
-/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
variable {D A : Type*} [Fintype D] [DecidableEq D] [Fintype A] [DecidableEq A]

lemma sum_fromBlocks {I R S T U : Type*} [Fintype I]
    (P : I → Matrix R T ℂ) (Q : I → Matrix R U ℂ)
    (R' : I → Matrix S T ℂ) (S' : I → Matrix S U ℂ) :
    (∑ i, Matrix.fromBlocks (P i) (Q i) (R' i) (S' i)) =
      Matrix.fromBlocks (∑ i, P i) (∑ i, Q i) (∑ i, R' i) (∑ i, S' i) := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.sum_apply]

theorem trace_blockDiagonal (X : Matrix D D ℂ) (Y : Matrix A A ℂ) :
    (Matrix.fromBlocks X 0 0 Y).trace = X.trace + Y.trace := by
  simp [Matrix.trace, Fintype.sum_sum_type]

theorem blockDiagonal_positive {X : Matrix D D ℂ} {Y : Matrix A A ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) : (Matrix.fromBlocks X 0 0 Y).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨hX.isHermitian.fromBlocks (by simp) hY.isHermitian, ?_⟩
  intro x
  rw [Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, add_zero, zero_add]
  have hstar : star x = Sum.elim (star (x ∘ Sum.inl)) (star (x ∘ Sum.inr)) := by
    funext i
    cases i <;> rfl
  rw [hstar, sumElim_dotProduct_sumElim]
  exact add_nonneg (hX.dotProduct_mulVec_nonneg _) (hY.dotProduct_mulVec_nonneg _)

lemma trace_kraus_sum {I : Type*} [Fintype I] (K : I → Matrix D A ℂ) (X : Matrix A A ℂ) :
    (∑ i, K i * X * (K i).conjTranspose).trace = ((∑ i, (K i).conjTranspose * K i) * X).trace := by
  rw [Matrix.trace_sum]
  conv_lhs => arg 2; ext i; rw [Matrix.trace_mul_cycle]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul]

structure HaltingInstrument (D A : Type*) [Fintype D] [Fintype A] [DecidableEq A] where
  exitRank : ℕ
  continueRank : ℕ
  exitKraus : Fin exitRank → Matrix D A ℂ
  continueKraus : Fin continueRank → Matrix A A ℂ
  normalized : (∑ i, (exitKraus i).conjTranspose * exitKraus i) +
    (∑ i, (continueKraus i).conjTranspose * continueKraus i) = 1

def HaltingInstrument.exit (I : HaltingInstrument D A) (X : Matrix A A ℂ) : Matrix D D ℂ :=
  ∑ i, I.exitKraus i * X * (I.exitKraus i).conjTranspose

def HaltingInstrument.continue (I : HaltingInstrument D A) (X : Matrix A A ℂ) : Matrix A A ℂ :=
  ∑ i, I.continueKraus i * X * (I.continueKraus i).conjTranspose

@[simp] theorem HaltingInstrument.exit_zero (I : HaltingInstrument D A) : I.exit 0 = 0 := by
  simp [HaltingInstrument.exit]
@[simp] theorem HaltingInstrument.continue_zero (I : HaltingInstrument D A) : I.continue 0 = 0 := by
  simp [HaltingInstrument.continue]

theorem HaltingInstrument.exit_positive (I : HaltingInstrument D A) {X : Matrix A A ℂ}
    (hX : X.PosSemidef) : (I.exit X).PosSemidef := by
  unfold HaltingInstrument.exit
  exact Finset.sum_induction _ _ (fun _ _ hU hV => hU.add hV) Matrix.PosSemidef.zero
    (fun i _ => hX.mul_mul_conjTranspose_same _)

theorem HaltingInstrument.continue_positive (I : HaltingInstrument D A) {X : Matrix A A ℂ}
    (hX : X.PosSemidef) : (I.continue X).PosSemidef := by
  unfold HaltingInstrument.continue
  exact Finset.sum_induction _ _ (fun _ _ hU hV => hU.add hV) Matrix.PosSemidef.zero
    (fun i _ => hX.mul_mul_conjTranspose_same _)

theorem HaltingInstrument.trace_preserved (I : HaltingInstrument D A) (X : Matrix A A ℂ) :
    (I.exit X).trace + (I.continue X).trace = X.trace := by
  rw [HaltingInstrument.exit, HaltingInstrument.continue, trace_kraus_sum, trace_kraus_sum,
    ← Matrix.trace_add, ← Matrix.add_mul, I.normalized, Matrix.one_mul]

/-- The full channel's actual finite Kraus index records keep/exit/continue. -/
def HaltingInstrument.fullKraus (I : HaltingInstrument D A) :
    Unit ⊕ (Fin I.exitRank ⊕ Fin I.continueRank) → Matrix (D ⊕ A) (D ⊕ A) ℂ
  | .inl _ => Matrix.fromBlocks 1 0 0 0
  | .inr (.inl i) => Matrix.fromBlocks 0 (I.exitKraus i) 0 0
  | .inr (.inr i) => Matrix.fromBlocks 0 0 0 (I.continueKraus i)

theorem HaltingInstrument.fullKraus_normalized (I : HaltingInstrument D A) :
    (∑ i, (I.fullKraus i).conjTranspose * I.fullKraus i) = 1 := by
  simp only [Fintype.sum_sum_type, Fintype.sum_unique, HaltingInstrument.fullKraus,
    Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    zero_add, add_zero]
  rw [sum_fromBlocks, sum_fromBlocks]
  simp only [Finset.sum_const_zero, Matrix.fromBlocks_add, add_zero, zero_add]
  rw [I.normalized]
  exact Matrix.fromBlocks_one

def HaltingInstrument.channel (I : HaltingInstrument D A) : FiniteChannel (D ⊕ A) (D ⊕ A) :=
  FiniteChannel.ofKraus I.fullKraus I.fullKraus_normalized

/-- Existing completed output is preserved by literal channel evaluation. -/
theorem HaltingInstrument.channel_apply (I : HaltingInstrument D A)
    (Y : Matrix D D ℂ) (X : Matrix A A ℂ) :
    I.channel.apply (Matrix.fromBlocks Y 0 0 X) =
      Matrix.fromBlocks (Y + I.exit X) 0 0 (I.continue X) := by
  rw [HaltingInstrument.channel, FiniteChannel.ofKraus_apply]
  simp only [Fintype.sum_sum_type, Fintype.sum_unique, HaltingInstrument.fullKraus,
    Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    zero_add, add_zero]
  rw [sum_fromBlocks, sum_fromBlocks]
  simp only [Finset.sum_const_zero, Matrix.fromBlocks_add, add_zero, zero_add]
  rfl

end OptimalQLS.LowerBounds
