import OptimalQLS.GraphEncoding.Construction

/-! # A uniform two-query circuit for the physical graph encoding -/
noncomputable section
set_option synthInstance.maxSize 1024
namespace OptimalQLS.GraphEncoding
open Matrix PolynomialTransform
open scoped Kronecker
variable {S D W C B V : Type*} [Fintype S] [DecidableEq S]
  [Fintype D] [DecidableEq D] [Fintype W] [DecidableEq W]
  [Fintype C] [DecidableEq C] [Fintype B] [DecidableEq B]
  [Fintype V] [DecidableEq V]

/-- Oracle placement with a literal spectator register, no oracle-dependent wiring. -/
def tensorPort (W C : Type*) [Fintype C] : QueryPort W (C × W) where
  multiplicity := Fintype.card C
  wiring := (Equiv.prodCongr (Equiv.refl W) (Fintype.equivFin C).symm).trans (Equiv.prodComm W C)
  control := fun _ => true

theorem tensorPort_apply (U : Matrix.unitaryGroup W ℂ) :
    (tensorPort W C).apply U = tensorUnitary (1 : Matrix.unitaryGroup C ℂ) U := by
  apply Subtype.ext
  ext ⟨c,i⟩ ⟨d,j⟩
  simp [tensorPort, QueryPort.apply, rewireUnitary, controlledUnitary,
    Matrix.blockDiagonal_apply, tensorUnitary, TransducerCompiler.HadamardClock.tensorUnitary,
    Matrix.kronecker_apply, Matrix.one_apply]

def rewirePort (e : W ≃ V) : QueryPort W V where
  multiplicity := 1
  wiring := (Equiv.prodUnique W (Fin 1)).trans e
  control := fun _ => true

theorem rewirePort_apply (e : W ≃ V) (U : Matrix.unitaryGroup W ℂ) :
    (rewirePort e).apply U = rewireUnitary e U := by
  apply Subtype.ext
  ext i j
  simp [rewirePort, QueryPort.apply, rewireUnitary, controlledUnitary,
    Matrix.blockDiagonal_apply]

/-- H, controlled U† and U, and H: chosen before the input oracle's values. -/
def signalCircuit (W B : Type*) [Fintype W] [DecidableEq W] : QueryCircuit W B (W ⊕ W) :=
  [.work (sumHadamard W)⁻¹] ++ hermitianizationCircuit W B ++ [.work (sumHadamard W)]

theorem signalCircuit_eval (U : Matrix.unitaryGroup W ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (signalCircuit W B).eval U Ub = hermitianSignal U := by
  simp [signalCircuit, QueryCircuit.eval_append, QueryCircuit.eval, QueryInstruction.eval,
    hermitianizationCircuit_eval, hermitianSignal, mul_assoc]

theorem signalCircuit_counts :
    (signalCircuit W B).matrixQueries = 2 ∧ (signalCircuit W B).vectorQueries = 0 ∧
      workInstructions (signalCircuit W B) = 3 := by
  simp [signalCircuit, hermitianizationCircuit, QueryCircuit.matrixQueries,
    QueryCircuit.vectorQueries, workInstructions]

/-- This circuit implements the first SELECT branch with only constant-size work matrices. -/
def branchCircuit (S D B : Type*) [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D] :
    QueryCircuit (S × D) B (BranchSpace S D) :=
  (signalCircuit (S × D) B).lift (tensorPort ((S × D) ⊕ (S × D)) Label) ++
    [.work (tensorUnitary (labelUnitary 1 (by decide)) 1)]

theorem tensorUnitary_mul (U V : Matrix.unitaryGroup C ℂ) (X Y : Matrix.unitaryGroup W ℂ) :
    tensorUnitary U X * tensorUnitary V Y = tensorUnitary (U*V) (X*Y) := by
  apply Subtype.ext
  change (U.val ⊗ₖ X.val) * (V.val ⊗ₖ Y.val) = (U.val*V.val) ⊗ₖ (X.val*Y.val)
  exact (Matrix.mul_kronecker_mul U.val V.val X.val Y.val).symm

theorem branchCircuit_eval (U : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (branchCircuit S D B).eval U Ub = branchA U := by
  simp only [branchCircuit, QueryCircuit.eval_append, QueryCircuit.eval, QueryInstruction.eval,
    one_mul, QueryCircuit.lift_eval, signalCircuit_eval, tensorPort_apply, tensorUnitary_mul,
    mul_one, one_mul, branchA]

theorem branchCircuit_counts :
    (branchCircuit S D B).matrixQueries = 2 ∧ (branchCircuit S D B).vectorQueries = 0 := by
  simp [branchCircuit, QueryCircuit.matrixQueries_append, QueryCircuit.vectorQueries_append,
    (QueryCircuit.lift_counts _ _).1, (QueryCircuit.lift_counts _ _).2,
    signalCircuit_counts.1, signalCircuit_counts.2.1,
    QueryCircuit.matrixQueries, QueryCircuit.vectorQueries]

/-- One literal two-term SELECT; the scalar κ affects only the known one-bit mixing gates. -/
def selectCircuit (S D B : Type*) [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]
    (κ : ℝ) (hκ : 0 < κ) : QueryCircuit (S × D) B (BranchSpace S D ⊕ BranchSpace S D) :=
  [.work (weightedMix (BranchSpace S D) κ hκ)⁻¹] ++
    (branchCircuit S D B).lift (leftOraclePort (BranchSpace S D)) ++
    [.work (sumUnitary 1 (branchI S D)), .work (weightedMix (BranchSpace S D) κ hκ)]

theorem selectCircuit_eval (κ : ℝ) (hκ : 0 < κ)
    (U : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (selectCircuit S D B κ hκ).eval U Ub = weightedSelect κ hκ (branchA U) (branchI S D) := by
  simp only [selectCircuit, QueryCircuit.eval_append, QueryCircuit.eval, QueryInstruction.eval,
    one_mul, QueryCircuit.lift_eval, branchCircuit_eval, leftOraclePort_apply]
  unfold weightedSelect
  simp only [mul_assoc]
  rw [← mul_assoc (sumUnitary 1 _) (sumUnitary _ 1) _, sumUnitary_right_left]

/-- Final physical-register oracle program; independent of all entries of A and U_A. -/
def graphCircuit (S D B : Type*) [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]
    (κ : ℝ) (hκ : 0 < κ) : QueryCircuit (S × D) B (Signal S × (Fin 4 × D)) :=
  (selectCircuit S D B κ hκ).lift (rewirePort (physicalWiring S D))

theorem graphCircuit_eval (κ : ℝ) (hκ : 0 < κ)
    (U : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (graphCircuit S D B κ hκ).eval U Ub = graphEncoding κ hκ U := by
  rw [graphCircuit, QueryCircuit.lift_eval, selectCircuit_eval, rewirePort_apply]
  rfl

theorem graphCircuit_counts (κ : ℝ) (hκ : 0 < κ) :
    (graphCircuit S D B κ hκ).matrixQueries = 2 ∧
      (graphCircuit S D B κ hκ).vectorQueries = 0 := by
  simp [graphCircuit, selectCircuit, QueryCircuit.matrixQueries_append,
    QueryCircuit.vectorQueries_append, (QueryCircuit.lift_counts _ _).1,
    (QueryCircuit.lift_counts _ _).2, branchCircuit_counts.1, branchCircuit_counts.2,
    QueryCircuit.matrixQueries, QueryCircuit.vectorQueries]

/-- The same actual program works for every exact normalized oracle encoding every Hermitian A. -/
theorem uniform_graph_circuit [Nonempty D] (κ : ℝ) (hκ : 0 < κ) (s : S) :
    ∃ c : QueryCircuit (S × D) B (Signal S × (Fin 4 × D)),
      c.matrixQueries = 2 ∧ c.vectorQueries = 0 ∧
      ∀ (U : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ)
        (A : Matrix D D ℂ), A.IsHermitian → IsBlockEncoding s 1 0 U A →
        (c.eval U Ub).val.IsHermitian ∧
        IsBlockEncoding (signalZero s) (1+κ⁻¹) 0 (c.eval U Ub) (graphMatrix A κ) := by
  refine ⟨graphCircuit S D B κ hκ, (graphCircuit_counts κ hκ).1,
    (graphCircuit_counts κ hκ).2, ?_⟩
  intro U Ub A hA henc
  rw [graphCircuit_eval]
  exact ⟨graphEncoding_hermitian κ hκ U, graphEncoding_exact κ hκ s U A hA henc⟩

end OptimalQLS.GraphEncoding
