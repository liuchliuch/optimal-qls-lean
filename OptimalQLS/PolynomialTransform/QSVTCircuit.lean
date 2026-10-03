import OptimalQLS.PolynomialTransform.EvenDilation
import OptimalQLS.OracleComposition

/-! # Literal query instruction lists for QSP and oracle Hermitianization -/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Matrix Polynomial
variable {W D B : Type*} [Fintype W] [DecidableEq W] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B]

/-- Three known phase instructions surround each actual Hermitian-oracle call. -/
def hermitianQSPCircuit (E : Matrix W D ℂ) (hE : Eᴴ*E=1) (z₀ : Circle) :
    List Circle → QueryCircuit W B W
  | [] => [.work (reciprocalSignalPhase E hE z₀)]
  | z::zs => .work (reciprocalSignalPhase E hE z) :: .work (signalBasisPhase E hE) ::
      .matrixCall (wholeOraclePort W) false :: .work (signalBasisPhase E hE) ::
        hermitianQSPCircuit E hE z₀ zs

/-- Instruction-list semantics agrees with the proved oracle-space unitary product. -/
theorem hermitianQSPCircuit_eval (E : Matrix W D ℂ) (hE : Eᴴ*E=1) (z₀ : Circle)
    (zs : List Circle) (U : Matrix.unitaryGroup W ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (hermitianQSPCircuit E hE z₀ zs).eval U Ub=hermitianPhaseWord E hE U z₀ zs := by
  induction zs with
  | nil => simp [hermitianQSPCircuit,QueryCircuit.eval,QueryInstruction.eval,
      hermitianPhaseWord,unitaryPhaseWord]
  | cons z zs ih =>
    simp [hermitianQSPCircuit,QueryCircuit.eval,QueryInstruction.eval,ih,
      hermitianPhaseWord,unitaryPhaseWord,hermitianSignal,mul_assoc]

/-- Exact independent matrix, vector, and work-instruction accounting. -/
theorem hermitianQSPCircuit_counts (E : Matrix W D ℂ) (hE : Eᴴ*E=1) (z₀ : Circle)
    (zs : List Circle) :
    (hermitianQSPCircuit (B := B) E hE z₀ zs).matrixQueries=zs.length ∧
    (hermitianQSPCircuit (B := B) E hE z₀ zs).vectorQueries=0 ∧
    workInstructions (hermitianQSPCircuit (B := B) E hE z₀ zs)=3*zs.length+1 := by
  induction zs with
  | nil => simp [hermitianQSPCircuit,QueryCircuit.matrixQueries,QueryCircuit.vectorQueries,workInstructions]
  | cons z zs ih =>
    simp only [hermitianQSPCircuit,QueryCircuit.matrixQueries,QueryCircuit.vectorQueries,
      workInstructions,List.length_cons,ih.1,ih.2.1,ih.2.2]
    simp [Nat.mul_add,Nat.add_assoc]

/-- Explicit binary multiplicity wiring to two direct-sum sectors. -/
def productFinTwoSum (W : Type*) : W × Fin 2 ≃ W ⊕ W where
  toFun wi := if wi.2=0 then Sum.inl wi.1 else Sum.inr wi.1
  invFun w := match w with | Sum.inl i => (i,0) | Sum.inr i => (i,1)
  left_inv wi := by rcases wi with ⟨w,i⟩; fin_cases i <;> simp
  right_inv w := by cases w <;> simp

def leftOraclePort (W : Type*) : QueryPort W (W ⊕ W) where
  multiplicity := 2
  wiring := productFinTwoSum W
  control := fun j => decide (j=0)

def rightOraclePort (W : Type*) : QueryPort W (W ⊕ W) where
  multiplicity := 2
  wiring := productFinTwoSum W
  control := fun j => decide (j=1)

@[simp] theorem leftOraclePort_apply (U : Matrix.unitaryGroup W ℂ) :
    (leftOraclePort W).apply U=sumUnitary U 1 := by
  apply Subtype.ext
  ext i j
  cases i <;> cases j <;>
    simp [leftOraclePort,QueryPort.apply,rewireUnitary,controlledUnitary,productFinTwoSum,
      Matrix.blockDiagonal,sumUnitary]

@[simp] theorem rightOraclePort_apply (U : Matrix.unitaryGroup W ℂ) :
    (rightOraclePort W).apply U=sumUnitary 1 U := by
  apply Subtype.ext
  ext i j
  cases i <;> cases j <;>
    simp [rightOraclePort,QueryPort.apply,rewireUnitary,controlledUnitary,productFinTwoSum,
      Matrix.blockDiagonal,sumUnitary]

/-- One swap, one controlled U†, and one controlled U realize the dilation. -/
def hermitianizationCircuit (W B : Type*) [Fintype W] [DecidableEq W] : QueryCircuit W B (W ⊕ W) :=
  [.work swapPublicPrivate,.matrixCall (rightOraclePort W) true,.matrixCall (leftOraclePort W) false]

/-- The concrete input-oracle circuit equals the literal Hermitian unitary dilation. -/
theorem hermitianizationCircuit_eval (U : Matrix.unitaryGroup W ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (hermitianizationCircuit W B).eval U Ub=LowerBounds.hermitianUnitaryDilation U := by
  simp only [hermitianizationCircuit,QueryCircuit.eval,QueryInstruction.eval,
    Bool.false_eq_true,ite_false,ite_true,rightOraclePort_apply,leftOraclePort_apply,one_mul]
  apply Subtype.ext
  change (Matrix.fromBlocks (U : Matrix W W ℂ) 0 0 1 *
    Matrix.fromBlocks (1 : Matrix W W ℂ) 0 0 (U : Matrix W W ℂ)ᴴ) *
      Matrix.fromBlocks 0 (1 : Matrix W W ℂ) (1 : Matrix W W ℂ) 0=_
  simp [Matrix.fromBlocks_multiply,LowerBounds.hermitianUnitaryDilation,LowerBounds.hermitianDilation]

/-- Dilation has exact query counts and no dependence on the vector oracle. -/
theorem hermitianizationCircuit_counts :
    (hermitianizationCircuit W B).matrixQueries=2 ∧
    (hermitianizationCircuit W B).vectorQueries=0 ∧
    workInstructions (hermitianizationCircuit W B)=1 := by
  simp [hermitianizationCircuit,QueryCircuit.matrixQueries,QueryCircuit.vectorQueries,workInstructions]

/-- Replace every Hermitian signal query by the verified two-query dilation. -/
def dilatedQSPCircuit (E : Matrix W D ℂ) (hE : Eᴴ*E=1) (z₀ : Circle) (zs : List Circle) :
    QueryCircuit W B (W ⊕ W) :=
  (hermitianQSPCircuit (B := B) (duplicateInsertion E) (duplicateInsertion_isometry E hE) z₀ zs).substituteMatrix (hermitianizationCircuit W B)

theorem dilatedQSPCircuit_eval (E : Matrix W D ℂ) (hE : Eᴴ*E=1) (z₀ : Circle)
    (zs : List Circle) (U : Matrix.unitaryGroup W ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (dilatedQSPCircuit E hE z₀ zs).eval U Ub =
      hermitianPhaseWord (duplicateInsertion E) (duplicateInsertion_isometry E hE)
        (LowerBounds.hermitianUnitaryDilation U) z₀ zs := by
  rw [dilatedQSPCircuit,QueryCircuit.substituteMatrix_eval,hermitianizationCircuit_eval,
    hermitianQSPCircuit_eval]

theorem dilatedQSPCircuit_counts (E : Matrix W D ℂ) (hE : Eᴴ*E=1) (z₀ : Circle) (zs : List Circle) :
    (dilatedQSPCircuit (B := B) E hE z₀ zs).matrixQueries=2*zs.length ∧
    (dilatedQSPCircuit (B := B) E hE z₀ zs).vectorQueries=0 := by
  have h := QueryCircuit.substituteMatrix_counts (hermitianizationCircuit W B)
    (hermitianQSPCircuit (B := B) (duplicateInsertion E) (duplicateInsertion_isometry E hE) z₀ zs)
  simpa only [dilatedQSPCircuit,(hermitianQSPCircuit_counts _ _ _ _).1,
    (hermitianQSPCircuit_counts _ _ _ _).2.1,hermitianizationCircuit_counts.1,
    hermitianizationCircuit_counts.2.1,Nat.mul_zero,Nat.add_zero,Nat.mul_comm] using h

/-- Actual original-oracle instructions for coherent real-part QSVT. -/
def evenQSVTCircuit (E : Matrix W D ℂ) (hE : Eᴴ*E=1) (z₀ : Circle) (zs : List Circle) :
    QueryCircuit W B ((W ⊕ W) ⊕ (W ⊕ W)) :=
  [.work (sumHadamard (W ⊕ W))] ++
    (dilatedQSPCircuit E hE z₀ zs).lift (leftOraclePort (W ⊕ W)) ++
    (dilatedQSPCircuit E hE z₀⁻¹ (zs.map Inv.inv)).lift (rightOraclePort (W ⊕ W)) ++
    [.work (sumHadamard (W ⊕ W))]

theorem sumUnitary_right_left (U V : Matrix.unitaryGroup W ℂ) :
    sumUnitary 1 V*sumUnitary U 1=sumUnitary U V := by
  apply Subtype.ext
  change Matrix.fromBlocks (1 : Matrix W W ℂ) 0 0 V*Matrix.fromBlocks (U : Matrix W W ℂ) 0 0 1=
    Matrix.fromBlocks (U : Matrix W W ℂ) 0 0 (V : Matrix W W ℂ)
  simp [Matrix.fromBlocks_multiply]

/-- The full instruction list evaluates to the already proved concrete QSVT unitary. -/
theorem evenQSVTCircuit_eval (E : Matrix W D ℂ) (hE : Eᴴ*E=1) (z₀ : Circle)
    (zs : List Circle) (U : Matrix.unitaryGroup W ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (evenQSVTCircuit E hE z₀ zs).eval U Ub=evenQSVTUnitary E hE U z₀ zs := by
  simp only [evenQSVTCircuit,QueryCircuit.eval_append,QueryCircuit.eval,QueryInstruction.eval,
    one_mul,QueryCircuit.lift_eval,dilatedQSPCircuit_eval,leftOraclePort_apply,rightOraclePort_apply]
  unfold evenQSVTUnitary coherentAverage
  simp only [mul_assoc]
  rw [← mul_assoc (sumUnitary 1 _) (sumUnitary _ 1) _,sumUnitary_right_left]

theorem evenQSVTCircuit_counts (E : Matrix W D ℂ) (hE : Eᴴ*E=1) (z₀ : Circle) (zs : List Circle) :
    (evenQSVTCircuit (B := B) E hE z₀ zs).matrixQueries=4*zs.length ∧
    (evenQSVTCircuit (B := B) E hE z₀ zs).vectorQueries=0 := by
  simp only [evenQSVTCircuit,QueryCircuit.matrixQueries_append,QueryCircuit.vectorQueries_append,
    QueryCircuit.matrixQueries,QueryCircuit.vectorQueries,
    (QueryCircuit.lift_counts _ _).1,(QueryCircuit.lift_counts _ _).2,
    (dilatedQSPCircuit_counts E hE z₀ zs).1,(dilatedQSPCircuit_counts E hE z₀ zs).2,
    (dilatedQSPCircuit_counts E hE z₀⁻¹ (zs.map Inv.inv)).1,
    (dilatedQSPCircuit_counts E hE z₀⁻¹ (zs.map Inv.inv)).2,List.length_map]
  constructor
  · omega
  · trivial

/-- General bounded even transformation with a literal oracle-independent
program and an explicit matrix-query constant. -/
theorem bounded_even_query_circuit (E : Matrix W D ℂ) (hE : Eᴴ*E=1)
    (p : ℝ[X]) (hp : Function.Even p.eval)
    (hbound : ∀ x : ℝ, |x| ≤ 1 → |p.eval x| ≤ 1) :
    ∃ c : QueryCircuit W B ((W ⊕ W) ⊕ (W ⊕ W)),
      c.matrixQueries ≤ 4*p.natDegree ∧ c.vectorQueries=0 ∧
      ∀ (U : Matrix.unitaryGroup W ℂ) (Ub : Matrix.unitaryGroup B ℂ) (A : Matrix D D ℂ),
        A.IsHermitian → Eᴴ*(U : Matrix W W ℂ)*E=A →
        (evenQSVTInsertion E)ᴴ*(c.eval U Ub : Matrix _ _ ℂ)*evenQSVTInsertion E =
          Polynomial.aeval A (liftReal p) := by
  obtain ⟨z₀,zs,hlen,htransform⟩ := bounded_even_matrix_transformation E hE p hp hbound
  refine ⟨evenQSVTCircuit E hE z₀ zs,?_,(evenQSVTCircuit_counts E hE z₀ zs).2,?_⟩
  · rw [(evenQSVTCircuit_counts E hE z₀ zs).1]
    omega
  · intro U Ub A hA hb
    rw [evenQSVTCircuit_eval]
    exact htransform U A hA hb


end OptimalQLS.PolynomialTransform
