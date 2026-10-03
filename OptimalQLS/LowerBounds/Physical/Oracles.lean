import OptimalQLS.LowerBounds.Physical.Embedding

/-! Explicit full physical oracle extensions, including all inactive columns. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
set_option linter.unusedSectionVars false
namespace OptimalQLS.LowerBounds.Physical
open Matrix PhysicalPadding
attribute [local instance] Classical.propDecidable
variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

/-- On the unused data coordinates the signal bit is flipped. In particular,
the complete signal-zero compression vanishes there. -/
def inactiveEncoding (f : D ↪ P) : Matrix.unitaryGroup (SignalIndex 1 × Inactive f) ℂ :=
  TransducerCompiler.permutation
    (Equiv.prodCongr (Equiv.swap (0 : SignalIndex 1) 1) (Equiv.refl (Inactive f)))

@[simp] theorem inactiveEncoding_zero_block (f : D ↪ P) (i j : Inactive f) :
    inactiveEncoding f (0,i) (0,j) = 0 := by
  simp [inactiveEncoding, TransducerCompiler.permutation, PEquiv.toMatrix]

/-- Wiring includes every physical computational basis state exactly once. -/
def signalPaddingCoordinates (f : D ↪ P) :
    ((SignalIndex 1 × D) ⊕ (SignalIndex 1 × Inactive f)) ≃ SignalIndex 1 × P :=
  (distributeSignalSum (SignalIndex 1) D (Inactive f)).trans
    (Equiv.prodCongr (Equiv.refl _) (paddingCoordinates f))

@[simp] theorem signalPaddingCoordinates_active (f : D ↪ P) (s : SignalIndex 1) (i : D) :
    signalPaddingCoordinates f (.inl (s,i)) = (s,f i) := rfl

@[simp] theorem signalPaddingCoordinates_inactive (f : D ↪ P) (s : SignalIndex 1) (i : Inactive f) :
    signalPaddingCoordinates f (.inr (s,i)) = (s,i.val) := rfl

@[simp] theorem signalPaddingCoordinates_symm_active (f : D ↪ P) (s : SignalIndex 1) (i : D) :
    (signalPaddingCoordinates f).symm (s,f i) = .inl (s,i) := by
  apply (signalPaddingCoordinates f).injective
  simp

@[simp] theorem signalPaddingCoordinates_symm_inactive (f : D ↪ P) (s : SignalIndex 1) (i : Inactive f) :
    (signalPaddingCoordinates f).symm (s,i.val) = .inr (s,i) := by
  apply (signalPaddingCoordinates f).injective
  simp

def extendEncoding (f : D ↪ P) (U : Matrix.unitaryGroup (SignalIndex 1 × D) ℂ) :
    Matrix.unitaryGroup (SignalIndex 1 × P) ℂ :=
  OptimalQLS.rewireUnitary (signalPaddingCoordinates f) (blockSumUnitary U (inactiveEncoding f))

theorem extendEncoding_signalBlock (f : D ↪ P) (U : Matrix.unitaryGroup (SignalIndex 1 × D) ℂ) :
    OptimalQLS.signalBlock (0 : SignalIndex 1) (extendEncoding f U) =
      zeroExtend f (OptimalQLS.signalBlock (0 : SignalIndex 1) U) := by
  ext i j
  obtain ⟨i, rfl⟩ := (paddingCoordinates f).surjective i
  obtain ⟨j, rfl⟩ := (paddingCoordinates f).surjective j
  rw [zeroExtend_in_coordinates, OptimalQLS.signalBlock_entries]
  cases i <;> cases j <;>
    simp [extendEncoding, OptimalQLS.rewireUnitary, blockSumUnitary,
      OptimalQLS.signalBlock_entries]

theorem extendEncoding_exact [Nonempty D] [Nonempty P] (f : D ↪ P)
    (U : Matrix.unitaryGroup (SignalIndex 1 × D) ℂ) (A : Matrix D D ℂ)
    (h : OptimalQLS.IsBlockEncoding (0 : SignalIndex 1) 1 0 U A) :
    OptimalQLS.IsBlockEncoding (0 : SignalIndex 1) 1 0 (extendEncoding f U) (zeroExtend f A) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [one_smul, extendEncoding_signalBlock]
  have he := OptimalQLS.exact_block_eq h
  rw [one_smul] at he
  rw [← he, sub_self, norm_zero]

def extendEncodingPolynomial {m : ℕ} (f : D ↪ P)
    (Q : Matrix (SignalIndex 1 × D) (SignalIndex 1 × D) (InputPolynomial m)) :
    Matrix (SignalIndex 1 × P) (SignalIndex 1 × P) (InputPolynomial m) :=
  (Matrix.fromBlocks Q 0 0 (constantPolynomialMatrix (inactiveEncoding f).val)).submatrix
    (signalPaddingCoordinates f).symm (signalPaddingCoordinates f).symm

theorem extendEncodingPolynomial_eval {m : ℕ} (f : D ↪ P)
    (Q : Matrix (SignalIndex 1 × D) (SignalIndex 1 × D) (InputPolynomial m))
    (U : Matrix.unitaryGroup (SignalIndex 1 × D) ℂ) (z : BitString m)
    (h : evalMatrix z Q = U.val) :
    evalMatrix z (extendEncodingPolynomial f Q) = (extendEncoding f U).val := by
  simp only [extendEncodingPolynomial, evalMatrix_submatrix, evalMatrix_fromBlocks,
    evalMatrix_zero, evalMatrix_constant, h]
  rfl

theorem extendEncodingPolynomial_degree {m : ℕ} (f : D ↪ P)
    (Q : Matrix (SignalIndex 1 × D) (SignalIndex 1 × D) (InputPolynomial m))
    (h : MatrixDegreeLE Q 1) : MatrixDegreeLE (extendEncodingPolynomial f Q) 1 :=
  matrixDegree_submatrix
    (matrixDegree_fromBlocks h matrixDegree_zero matrixDegree_zero (matrixDegree_constant _)) _ _

/-- Every logical exact promise yields a strict full-zero-extension promise
for the explicitly constructed whole oracles. -/
theorem extendExactPromise {d : ℕ} [NeZero d] {kappa estimate eps : ℝ}
    (A : Matrix (Fin d) (Fin d) ℂ) (b : DataSpace d)
    (UA : Matrix.unitaryGroup (SignalIndex 1 × Fin d) ℂ)
    (Ub : Matrix.unitaryGroup (Fin d) ℂ)
    (h : ExactQLSPromise (canonicalLowerParameters kappa estimate eps) A b UA Ub) :
    PhysicalExactQLSPromise (canonicalLowerParameters kappa estimate eps) A b
      (extendEncoding (activeIndex d) UA) (extendUnitary (activeIndex d) Ub) := by
  refine ⟨⟨h.invertible, h.unitVector, extendEncoding_exact (activeIndex d) UA A h.exactEncoding,
    ?_, h.kappaLower, h.inverseBound, h.epsilonPositive, h.epsilonUpper⟩,
    h.estimateLower, h.estimateUpper⟩
  intro i
  simpa using extendUnitary_prepares (activeIndex d) Ub 0 (WithLp.ofLp b) h.statePreparation i

end OptimalQLS.LowerBounds.Physical
