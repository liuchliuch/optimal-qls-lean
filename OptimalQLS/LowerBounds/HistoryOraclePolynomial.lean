import OptimalQLS.LowerBounds.PolynomialMatrix
import OptimalQLS.LowerBounds.HistoryQuerySimulation
import OptimalQLS.LowerBounds.NormControlledFamily

/-!
# Literal degree-one entry polynomials for the complete matrix oracle

The polynomial is constructed from the single-bit history transition, the
actual mixing/select/mixing LCU, fixed scalar encodings, direct sums and the
Hermitian oracle dilation. Its evaluation is proved equal to every entry of
the full oracle, including through controlled/adjoint query ports. This is a
derived polynomial representation, not an assumed degree certificate.
-/
noncomputable section
open scoped BigOperators
namespace OptimalQLS.LowerBounds
open Matrix MvPolynomial

/-- Entry polynomial of I or a single hidden-bit-controlled X. -/
def gatedXPolynomial {m : ℕ} (label : Option (Fin m)) (row col : Bool) : InputPolynomial m :=
  match label with
  | none => C (if row = col then 1 else 0)
  | some i => (1 - X i) * C (if row = col then 1 else 0) +
      X i * C (if row = !col then 1 else 0)

theorem gatedXPolynomial_eval {m : ℕ} (label : Option (Fin m)) (row col : Bool) (z : BitString m) :
    eval (bitValue z) (gatedXPolynomial label row col) =
      if row = Bool.xor col (labelBit z label) then (1 : ℂ) else 0 := by
  cases label with
  | none => cases row <;> cases col <;> simp [gatedXPolynomial, labelBit]
  | some i => cases row <;> cases col <;> cases hz : z i <;>
      simp [gatedXPolynomial, labelBit, bitValue, hz]

theorem gatedXPolynomial_degree {m : ℕ} (label : Option (Fin m)) (row col : Bool) :
    (gatedXPolynomial label row col).totalDegree ≤ 1 := by
  cases label with
  | none =>
    change (C (if row = col then (1 : ℂ) else 0) : InputPolynomial m).totalDegree ≤ 1
    simp only [MvPolynomial.totalDegree_C]
    omega
  | some i =>
    apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · apply (MvPolynomial.totalDegree_mul _ _).trans
      have hsub : (1 - X i : InputPolynomial m).totalDegree ≤ 1 :=
        (MvPolynomial.totalDegree_sub _ _).trans (by simp)
      simpa only [MvPolynomial.totalDegree_C, Nat.add_zero] using hsub
    · apply (MvPolynomial.totalDegree_mul _ _).trans
      simp only [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
      omega

theorem forwardPermutation_entry {D : Type*} [Fintype D] [DecidableEq D]
    (p : Equiv.Perm D) (i j : D) :
    (Matrix.permMatrixHom (R := ℂ) p) i j = if i = p j then 1 else 0 := by
  by_cases h : i = p j
  · subst i
    simp [Matrix.permMatrixHom, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  · have hj : j ≠ p.symm i := by
      intro he
      have he' : p j = i := (Equiv.eq_symm_apply p).mp he
      exact h he'.symm
    simp [Matrix.permMatrixHom, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, h, Ne.symm hj]

theorem historyPermutation_label_apply {N ell m : ℕ} [NeZero N] [NeZero m]
    (hell : 0 < ell) (hN : N = 2 * ell + 2 * m) (z : BitString m) (j : Fin N) (b : Bool) :
    historyPermutation (fixedParityProfile ell z) (j, b) =
      (j + 1, Bool.xor b (labelBit z (parityHistoryLabel hell hN j))) := by
  have h := parityHistoryStep_twoQuery_clean hell hN z j b
  rw [twoQueryHistoryStep_clean] at h
  exact (congrArg (fun x : SimulationBasis N m => x.2.2) h).symm

def historyStepPolynomial {N ell m : ℕ} [NeZero N]
    (hell : 0 < ell) (hN : N = 2 * ell + 2 * m) :
    Matrix (HistoryBasis N) (HistoryBasis N) (InputPolynomial m) :=
  fun row col => if row.1 = col.1 + 1 then
    gatedXPolynomial (parityHistoryLabel hell hN col.1) row.2 col.2 else 0

theorem historyStepPolynomial_eval {N ell m : ℕ} [NeZero N] [NeZero m]
    (hell : 0 < ell) (hN : N = 2 * ell + 2 * m) (z : BitString m) :
    evalMatrix z (historyStepPolynomial hell hN) = historyStep (fixedParityProfile ell z) := by
  ext row col
  rcases row with ⟨i, b⟩
  rcases col with ⟨j, c⟩
  rw [historyStep, forwardPermutation_entry, historyPermutation_label_apply hell hN z j c]
  by_cases hij : i = j + 1 <;>
    simp [evalMatrix, historyStepPolynomial, hij, gatedXPolynomial_eval, Prod.mk.injEq]

theorem historyStepPolynomial_degree {N ell m : ℕ} [NeZero N]
    (hell : 0 < ell) (hN : N = 2 * ell + 2 * m) : MatrixDegreeLE (historyStepPolynomial hell hN) 1 := by
  intro i j
  unfold historyStepPolynomial
  split_ifs
  · exact gatedXPolynomial_degree _ _ _
  · simp

variable {D E S : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
  [Fintype S] [DecidableEq S]

def lcuPolynomial {m : ℕ} (P : Matrix D D (InputPolynomial m)) (r : ℝ) :
    Matrix (Bool × D) (Bool × D) (InputPolynomial m) :=
  (constantPolynomialMatrix (OptimalQLS.fractionalMix (n := D) r) *
    Matrix.fromBlocks 1 0 0 (-P) * constantPolynomialMatrix (OptimalQLS.fractionalMix (n := D) r)).submatrix
      (sumBoolEquiv D).symm (sumBoolEquiv D).symm

theorem lcuPolynomial_eval {m : ℕ} (P : Matrix D D (InputPolynomial m))
    (r : ℝ) (hr : |r| < 1) (U : Matrix.unitaryGroup D ℂ) (z : BitString m)
    (hP : evalMatrix z P = (U : Matrix D D ℂ)) :
    evalMatrix z (lcuPolynomial P r) = (twoTermLCU U r hr : Matrix (Bool × D) (Bool × D) ℂ) := by
  simp only [lcuPolynomial, evalMatrix_submatrix, evalMatrix_mul, evalMatrix_constant,
    evalMatrix_fromBlocks, evalMatrix_one, evalMatrix_zero, evalMatrix_neg, hP]
  rfl

theorem lcuPolynomial_degree {m d : ℕ} {P : Matrix D D (InputPolynomial m)} (r : ℝ)
    (hP : MatrixDegreeLE P d) : MatrixDegreeLE (lcuPolynomial P r) d := by
  apply matrixDegree_submatrix
  have hs : MatrixDegreeLE (Matrix.fromBlocks (1 : Matrix D D (InputPolynomial m)) 0 0 (-P)) d :=
    matrixDegree_fromBlocks matrixDegree_one matrixDegree_zero matrixDegree_zero (matrixDegree_neg hP)
  simpa using matrixDegree_mul (matrixDegree_mul
    (matrixDegree_constant (d := 0) (OptimalQLS.fractionalMix (n := D) r)) hs)
    (matrixDegree_constant (d := 0) (OptimalQLS.fractionalMix (n := D) r))

def polynomialSumEncoding {m : ℕ} (P : Matrix (S × D) (S × D) (InputPolynomial m))
    (Q : Matrix (S × E) (S × E) (InputPolynomial m)) : Matrix (S × (D ⊕ E)) (S × (D ⊕ E)) (InputPolynomial m) :=
  (Matrix.fromBlocks P 0 0 Q).submatrix (distributeSignalSum S D E).symm (distributeSignalSum S D E).symm

theorem polynomialSumEncoding_eval {m : ℕ}
    (P : Matrix (S × D) (S × D) (InputPolynomial m)) (Q : Matrix (S × E) (S × E) (InputPolynomial m))
    (U : Matrix.unitaryGroup (S × D) ℂ) (V : Matrix.unitaryGroup (S × E) ℂ) (z : BitString m)
    (hP : evalMatrix z P = (U : Matrix (S × D) (S × D) ℂ))
    (hQ : evalMatrix z Q = (V : Matrix (S × E) (S × E) ℂ)) :
    evalMatrix z (polynomialSumEncoding P Q) = (sumEncoding U V : Matrix (S × (D ⊕ E)) (S × (D ⊕ E)) ℂ) := by
  simp only [polynomialSumEncoding, evalMatrix_submatrix, evalMatrix_fromBlocks, evalMatrix_zero, hP, hQ]
  rfl

theorem polynomialSumEncoding_degree {m d : ℕ}
    {P : Matrix (S × D) (S × D) (InputPolynomial m)} {Q : Matrix (S × E) (S × E) (InputPolynomial m)}
    (hP : MatrixDegreeLE P d) (hQ : MatrixDegreeLE Q d) : MatrixDegreeLE (polynomialSumEncoding P Q) d :=
  matrixDegree_submatrix (matrixDegree_fromBlocks hP matrixDegree_zero matrixDegree_zero hQ) _ _

def polynomialDilationEncoding {m : ℕ} (P : Matrix (S × D) (S × D) (InputPolynomial m)) :
    Matrix (S × (D ⊕ D)) (S × (D ⊕ D)) (InputPolynomial m) :=
  (Matrix.fromBlocks 0 P (polynomialAdjoint P) 0).submatrix
    (distributeSignal S D).symm (distributeSignal S D).symm

theorem polynomialDilationEncoding_eval {m : ℕ}
    (P : Matrix (S × D) (S × D) (InputPolynomial m)) (U : Matrix.unitaryGroup (S × D) ℂ)
    (z : BitString m) (hP : evalMatrix z P = (U : Matrix (S × D) (S × D) ℂ)) :
    evalMatrix z (polynomialDilationEncoding P) = (dilationEncoding U : Matrix (S × (D ⊕ D)) (S × (D ⊕ D)) ℂ) := by
  simp only [polynomialDilationEncoding, evalMatrix_submatrix, evalMatrix_fromBlocks,
    evalMatrix_zero, evalMatrix_adjoint, hP]
  rfl

theorem polynomialDilationEncoding_degree {m d : ℕ}
    {P : Matrix (S × D) (S × D) (InputPolynomial m)} (hP : MatrixDegreeLE P d) :
    MatrixDegreeLE (polynomialDilationEncoding P) d :=
  matrixDegree_submatrix (matrixDegree_fromBlocks matrixDegree_zero hP
    (matrixDegree_adjoint hP) matrixDegree_zero) _ _

/-- Explicit entry polynomial of the full norm-controlled Hermitian matrix oracle. -/
def hardFamilyPolynomial {N m : ℕ} [NeZero N] {kappa : ℝ} (hk : 4 ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) :
    Matrix (Bool × HardFamilyIndex N) (Bool × HardFamilyIndex N) (InputPolynomial m) :=
  polynomialDilationEncoding (polynomialSumEncoding
    (constantPolynomialMatrix (1 : Matrix (Bool × Unit) (Bool × Unit) ℂ))
    (polynomialSumEncoding
      (lcuPolynomial (historyStepPolynomial (historyPadding_pos hk) hN) (lcuMixingParameter (historyLambda kappa)))
      (constantPolynomialMatrix (scalarEncoding kappa⁻¹ (kappa_inv_abs_lt_one hk) :
        Matrix (Bool × Unit) (Bool × Unit) ℂ))))

/-- Every entry of the complete oracle really evaluates to the constructed U_A,z. -/
theorem hardFamilyPolynomial_eval {N m : ℕ} [NeZero N] [NeZero m] {kappa : ℝ}
    (hk : 4 ≤ kappa) (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    evalMatrix z (hardFamilyPolynomial hk hN) =
      (hardFamilyEncoding (N := N) hk z : Matrix (Bool × HardFamilyIndex N) (Bool × HardFamilyIndex N) ℂ) := by
  unfold hardFamilyPolynomial hardFamilyEncoding
  apply polynomialDilationEncoding_eval
  apply polynomialSumEncoding_eval
  · exact evalMatrix_constant _ _
  · apply polynomialSumEncoding_eval
    · apply lcuPolynomial_eval
      exact historyStepPolynomial_eval (historyPadding_pos hk) hN z
    · exact evalMatrix_constant _ _

/-- The full oracle, not just its encoded block, has total entry degree≤1. -/
theorem hardFamilyPolynomial_degree {N m : ℕ} [NeZero N] {kappa : ℝ}
    (hk : 4 ≤ kappa) (hN : N = 2 * historyPadding kappa + 2 * m) :
    MatrixDegreeLE (hardFamilyPolynomial hk hN) 1 := by
  apply polynomialDilationEncoding_degree
  apply polynomialSumEncoding_degree (matrixDegree_constant _)
  apply polynomialSumEncoding_degree
  · exact lcuPolynomial_degree _ (historyStepPolynomial_degree _ _)
  · exact matrixDegree_constant _

/-- Full adjoint/controlled query ports also have proved degree≤1 and exact
operational evaluation, with arbitrary finite reference/workspace wiring. -/
theorem hardFamily_polynomialPort {N m : ℕ} [NeZero N] [NeZero m] {kappa : ℝ}
    {W : Type*} [Fintype W] [DecidableEq W] (hk : 4 ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m)
    (port : OptimalQLS.QueryPort (Bool × HardFamilyIndex N) W) (adjoint : Bool) :
    MatrixDegreeLE (polynomialPort port adjoint (hardFamilyPolynomial hk hN)) 1 ∧
    ∀ z : BitString m, evalMatrix z (polynomialPort port adjoint (hardFamilyPolynomial hk hN)) =
      (port.apply (if adjoint then (hardFamilyEncoding (N := N) hk z)⁻¹ else hardFamilyEncoding hk z) : Matrix W W ℂ) := by
  refine ⟨polynomialPort_degree port adjoint (hardFamilyPolynomial_degree hk hN), ?_⟩
  intro z
  exact polynomialPort_eval _ _ _ _ z (hardFamilyPolynomial_eval hk hN z)

end OptimalQLS.LowerBounds
