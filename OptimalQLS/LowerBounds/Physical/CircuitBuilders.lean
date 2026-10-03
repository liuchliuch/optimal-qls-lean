import OptimalQLS.LowerBounds.Physical.HistoryBitCircuit

/-! Explicit fixed gate-word constructors for LCU, augmentation and dilation. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace OptimalQLS.LowerBounds.Physical
open Matrix
variable {A B S D E W V : Type*}
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
  [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]

theorem rewire_blockSum_swap (U : Matrix.unitaryGroup W ℂ) (R : Matrix.unitaryGroup V ℂ) :
    rewireUnitary (Equiv.sumComm W V) (blockSumUnitary U R) = blockSumUnitary R U := by
  apply Subtype.ext
  ext i j
  cases i <;> cases j <;> rfl

def sumRightCircuit (p : QueryPort A V) (q : QueryPort B V) (c : QueryCircuit A B W) :
    QueryCircuit A B (V ⊕ W) :=
  rewireCircuit (Equiv.sumComm W V) (sumLeftCircuit p q c)

theorem sumRightCircuit_eval (p : QueryPort A V) (q : QueryPort B V)
    (c : QueryCircuit A B W) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (sumRightCircuit p q c).eval UA Ub = blockSumUnitary 1 (c.eval UA Ub) := by
  rw [sumRightCircuit, rewireCircuit_eval, sumLeftCircuit_eval, rewire_blockSum_swap]

theorem sumRightCircuit_counts (p : QueryPort A V) (q : QueryPort B V) (c : QueryCircuit A B W) :
    (sumRightCircuit p q c).matrixQueries = c.matrixQueries ∧
      (sumRightCircuit p q c).vectorQueries = c.vectorQueries := by
  rw [sumRightCircuit]
  exact ⟨(rewireCircuit_counts _ _).1.trans (sumLeftCircuit_counts _ _ _).1,
    (rewireCircuit_counts _ _).2.trans (sumLeftCircuit_counts _ _ _).2⟩

/-- Concrete mixing, controlled query word, fixed minus sign, and mixing. -/
def lcuCircuit (p : QueryPort A W) (q : QueryPort B W) (c : QueryCircuit A B W)
    (r : ℝ) (hr : |r| < 1) : QueryCircuit A B (Bool × W) :=
  rewireCircuit (sumBoolEquiv W)
    ([.work ⟨fractionalMix r, fractionalMix_unitary hr⟩] ++
      sumRightCircuit p q c ++
      [.work (blockSumUnitary 1 (negativeUnitary (1 : Matrix.unitaryGroup W ℂ))),
       .work ⟨fractionalMix r, fractionalMix_unitary hr⟩])

theorem negativePrivate_factor (U : Matrix.unitaryGroup W ℂ) :
    blockSumUnitary 1 (negativeUnitary (1 : Matrix.unitaryGroup W ℂ)) * blockSumUnitary 1 U =
      privateOracle (negativeUnitary U) := by
  apply Subtype.ext
  simp [blockSumUnitary, negativeUnitary, privateOracle, Matrix.fromBlocks_multiply]

theorem lcuCircuit_eval (p : QueryPort A W) (q : QueryPort B W) (c : QueryCircuit A B W)
    (r : ℝ) (hr : |r| < 1) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (lcuCircuit p q c r hr).eval UA Ub = twoTermLCU (c.eval UA Ub) r hr := by
  simp only [lcuCircuit, rewireCircuit_eval, QueryCircuit.eval_append, QueryCircuit.eval,
    QueryInstruction.eval, one_mul, sumRightCircuit_eval]
  simp only [mul_assoc]
  rw [← mul_assoc (blockSumUnitary 1 (negativeUnitary (1 : Matrix.unitaryGroup W ℂ))),
    negativePrivate_factor]
  simp only [twoTermLCU, mul_assoc]

theorem lcuCircuit_counts (p : QueryPort A W) (q : QueryPort B W) (c : QueryCircuit A B W)
    (r : ℝ) (hr : |r| < 1) :
    (lcuCircuit p q c r hr).matrixQueries = c.matrixQueries ∧
      (lcuCircuit p q c r hr).vectorQueries = c.vectorQueries := by
  rw [lcuCircuit, (rewireCircuit_counts _ _).1, (rewireCircuit_counts _ _).2]
  simp [QueryCircuit.matrixQueries_append, QueryCircuit.vectorQueries_append,
    QueryCircuit.matrixQueries, QueryCircuit.vectorQueries,
    (sumRightCircuit_counts p q c).1, (sumRightCircuit_counts p q c).2]

/-- Add a fixed exact-encoding block on the right, without querying it. -/
def sumEncodingRightCircuit (p : QueryPort A (S × E)) (q : QueryPort B (S × E))
    (c : QueryCircuit A B (S × D)) (U : Matrix.unitaryGroup (S × E) ℂ) :
    QueryCircuit A B (S × (D ⊕ E)) :=
  rewireCircuit (distributeSignalSum S D E)
    (sumLeftCircuit p q c ++ [.work (blockSumUnitary 1 U)])

theorem sumEncodingRightCircuit_eval (p : QueryPort A (S × E)) (q : QueryPort B (S × E))
    (c : QueryCircuit A B (S × D)) (U : Matrix.unitaryGroup (S × E) ℂ)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (sumEncodingRightCircuit p q c U).eval UA Ub = sumEncoding (c.eval UA Ub) U := by
  simp only [sumEncodingRightCircuit, rewireCircuit_eval, QueryCircuit.eval_append,
    QueryCircuit.eval, QueryInstruction.eval, one_mul, sumLeftCircuit_eval,
    ← blockSumUnitary_mul, one_mul, mul_one]
  rfl

/-- Add a fixed exact-encoding block on the left, without querying it. -/
def sumEncodingLeftCircuit (p : QueryPort A (S × D)) (q : QueryPort B (S × D))
    (U : Matrix.unitaryGroup (S × D) ℂ) (c : QueryCircuit A B (S × E)) :
    QueryCircuit A B (S × (D ⊕ E)) :=
  rewireCircuit (distributeSignalSum S D E)
    (sumRightCircuit p q c ++ [.work (blockSumUnitary U 1)])

theorem sumEncodingLeftCircuit_eval (p : QueryPort A (S × D)) (q : QueryPort B (S × D))
    (U : Matrix.unitaryGroup (S × D) ℂ) (c : QueryCircuit A B (S × E))
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (sumEncodingLeftCircuit p q U c).eval UA Ub = sumEncoding U (c.eval UA Ub) := by
  simp only [sumEncodingLeftCircuit, rewireCircuit_eval, QueryCircuit.eval_append,
    QueryCircuit.eval, QueryInstruction.eval, one_mul, sumRightCircuit_eval,
    ← blockSumUnitary_mul, one_mul, mul_one]
  rfl

theorem sumEncodingRightCircuit_counts (p : QueryPort A (S × E)) (q : QueryPort B (S × E))
    (c : QueryCircuit A B (S × D)) (U : Matrix.unitaryGroup (S × E) ℂ) :
    (sumEncodingRightCircuit p q c U).matrixQueries = c.matrixQueries ∧
      (sumEncodingRightCircuit p q c U).vectorQueries = c.vectorQueries := by
  rw [sumEncodingRightCircuit, (rewireCircuit_counts _ _).1, (rewireCircuit_counts _ _).2]
  simp [QueryCircuit.matrixQueries_append, QueryCircuit.vectorQueries_append,
    QueryCircuit.matrixQueries, QueryCircuit.vectorQueries,
    (sumLeftCircuit_counts p q c).1, (sumLeftCircuit_counts p q c).2]

theorem sumEncodingLeftCircuit_counts (p : QueryPort A (S × D)) (q : QueryPort B (S × D))
    (U : Matrix.unitaryGroup (S × D) ℂ) (c : QueryCircuit A B (S × E)) :
    (sumEncodingLeftCircuit p q U c).matrixQueries = c.matrixQueries ∧
      (sumEncodingLeftCircuit p q U c).vectorQueries = c.vectorQueries := by
  rw [sumEncodingLeftCircuit, (rewireCircuit_counts _ _).1, (rewireCircuit_counts _ _).2]
  simp [QueryCircuit.matrixQueries_append, QueryCircuit.vectorQueries_append,
    QueryCircuit.matrixQueries, QueryCircuit.vectorQueries,
    (sumRightCircuit_counts p q c).1, (sumRightCircuit_counts p q c).2]

/-- The complete Hermitian dilation, using c and c-adjoint in their actual
respective halves; the first known gate exchanges the two halves. -/
def dilationCircuit (p : QueryPort A (S × D)) (q : QueryPort B (S × D))
    (c : QueryCircuit A B (S × D)) : QueryCircuit A B (S × (D ⊕ D)) :=
  rewireCircuit (distributeSignal S D)
    ([.work swapPublicPrivate] ++ sumLeftCircuit p q c ++ sumRightCircuit p q c.adjoint)

theorem dilationCircuit_eval (p : QueryPort A (S × D)) (q : QueryPort B (S × D))
    (c : QueryCircuit A B (S × D)) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (dilationCircuit p q c).eval UA Ub = dilationEncoding (c.eval UA Ub) := by
  simp only [dilationCircuit, rewireCircuit_eval, QueryCircuit.eval_append,
    QueryCircuit.eval, QueryInstruction.eval, one_mul, sumLeftCircuit_eval,
    sumRightCircuit_eval, QueryCircuit.adjoint_eval, ← mul_assoc,
    ← blockSumUnitary_mul, one_mul, mul_one]
  congr 1
  apply Subtype.ext
  simp [blockSumUnitary, swapPublicPrivate, hermitianUnitaryDilation, hermitianDilation,
    Matrix.fromBlocks_multiply, Matrix.UnitaryGroup.inv_val, Matrix.star_eq_conjTranspose]

theorem dilationCircuit_counts (p : QueryPort A (S × D)) (q : QueryPort B (S × D))
    (c : QueryCircuit A B (S × D)) :
    (dilationCircuit p q c).matrixQueries = 2*c.matrixQueries ∧
      (dilationCircuit p q c).vectorQueries = 2*c.vectorQueries := by
  rw [dilationCircuit, (rewireCircuit_counts _ _).1, (rewireCircuit_counts _ _).2]
  simp [QueryCircuit.matrixQueries_append, QueryCircuit.vectorQueries_append,
    QueryCircuit.matrixQueries, QueryCircuit.vectorQueries,
    (sumLeftCircuit_counts p q c).1, (sumLeftCircuit_counts p q c).2,
    (sumRightCircuit_counts p q c.adjoint).1, (sumRightCircuit_counts p q c.adjoint).2,
    (QueryCircuit.adjoint_counts c).1, (QueryCircuit.adjoint_counts c).2, two_mul]

end OptimalQLS.LowerBounds.Physical
