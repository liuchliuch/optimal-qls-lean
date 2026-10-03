import OptimalQLS.LowerBounds.HistoryBlockEncoding
import OptimalQLS.LowerBounds.HermitianDilation

/-! Exact same-signal block encodings for direct sums and scalar contractions. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
variable {S D E : Type*} [Fintype S] [DecidableEq S]
  [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

def blockSumUnitary (U : Matrix.unitaryGroup D ℂ) (V : Matrix.unitaryGroup E ℂ) :
    Matrix.unitaryGroup (D ⊕ E) ℂ :=
  ⟨Matrix.fromBlocks (U : Matrix D D ℂ) 0 0 (V : Matrix E E ℂ), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    have hU : (U : Matrix D D ℂ) * (U : Matrix D D ℂ).conjTranspose = 1 := U.property.2
    have hV : (V : Matrix E E ℂ) * (V : Matrix E E ℂ).conjTranspose = 1 := V.property.2
    simp [hU, hV]⟩

def distributeSignalSum (S D E : Type*) : ((S × D) ⊕ (S × E)) ≃ S × (D ⊕ E) where
  toFun x := match x with | .inl (s, d) => (s, .inl d) | .inr (s, e) => (s, .inr e)
  invFun x := match x.2 with | .inl d => .inl (x.1, d) | .inr e => .inr (x.1, e)
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨s, x⟩; cases x <;> rfl

def sumEncoding (U : Matrix.unitaryGroup (S × D) ℂ) (V : Matrix.unitaryGroup (S × E) ℂ) :
    Matrix.unitaryGroup (S × (D ⊕ E)) ℂ :=
  OptimalQLS.rewireUnitary (distributeSignalSum S D E) (blockSumUnitary U V)

theorem sumEncoding_signalBlock (s : S) (U : Matrix.unitaryGroup (S × D) ℂ)
    (V : Matrix.unitaryGroup (S × E) ℂ) :
    OptimalQLS.signalBlock s (sumEncoding U V : Matrix (S × (D ⊕ E)) (S × (D ⊕ E)) ℂ) =
      Matrix.fromBlocks (OptimalQLS.signalBlock s U) 0 0 (OptimalQLS.signalBlock s V) := by
  ext i j
  cases i <;> cases j <;>
    simp [OptimalQLS.signalBlock_entries, sumEncoding, OptimalQLS.rewireUnitary,
      distributeSignalSum, blockSumUnitary]

theorem sumEncoding_exact [Nonempty D] [Nonempty E] (s : S)
    (U : Matrix.unitaryGroup (S × D) ℂ) (V : Matrix.unitaryGroup (S × E) ℂ)
    (A : Matrix D D ℂ) (B : Matrix E E ℂ)
    (hA : OptimalQLS.IsBlockEncoding s 1 0 U A) (hB : OptimalQLS.IsBlockEncoding s 1 0 V B) :
    OptimalQLS.IsBlockEncoding s 1 0 (sumEncoding U V) (Matrix.fromBlocks A 0 0 B) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [one_smul, sumEncoding_signalBlock, OptimalQLS.exact_block_eq hA, OptimalQLS.exact_block_eq hB]
  simp

theorem identityEncoding_exact [Nonempty D] (s : S) :
    OptimalQLS.IsBlockEncoding s 1 0 (1 : Matrix.unitaryGroup (S × D) ℂ) (1 : Matrix D D ℂ) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  have hblock : OptimalQLS.signalBlock s (1 : Matrix (S × D) (S × D) ℂ) = 1 := by
    ext i j
    simp [OptimalQLS.signalBlock_entries, Matrix.one_apply]
  rw [one_smul]
  change ‖(1 : Matrix D D ℂ) - OptimalQLS.signalBlock s (1 : Matrix (S × D) (S × D) ℂ)‖ ≤ 0
  rw [hblock]
  simp

def scalarEncoding (c : ℝ) (hc : |c| < 1) : Matrix.unitaryGroup (Bool × Unit) ℂ :=
  OptimalQLS.rewireUnitary (sumBoolEquiv Unit)
    ⟨OptimalQLS.fractionalMix (-c), OptimalQLS.fractionalMix_unitary (by simpa using hc)⟩

theorem scalarEncoding_signalBlock (c : ℝ) (hc : |c| < 1) :
    OptimalQLS.signalBlock false (scalarEncoding c hc : Matrix (Bool × Unit) (Bool × Unit) ℂ) =
      c • (1 : Matrix Unit Unit ℂ) := by
  ext i j
  simp [OptimalQLS.signalBlock_entries, scalarEncoding, OptimalQLS.rewireUnitary,
    sumBoolEquiv, OptimalQLS.fractionalMix]

theorem scalarEncoding_exact (c : ℝ) (hc : |c| < 1) :
    OptimalQLS.IsBlockEncoding false 1 0 (scalarEncoding c hc) (c • (1 : Matrix Unit Unit ℂ)) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [one_smul, scalarEncoding_signalBlock]
  simp

end OptimalQLS.LowerBounds
