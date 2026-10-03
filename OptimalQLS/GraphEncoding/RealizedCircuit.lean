import OptimalQLS.GraphEncoding.SmallGates

/-! # A76-elementary-gate, two-query physical realization -/
noncomputable section
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace OptimalQLS.GraphEncoding
open Matrix PolynomialTransform TransducerCompiler
open scoped Kronecker
variable {W S D A B : Type*} [Fintype W] [DecidableEq W]
  [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def labelDistribution (W : Type*) : (Label ⊕ Label) × W ≃ (Label × W) ⊕ (Label × W) where
  toFun p := match p.1 with | .inl l => .inl (l,p.2) | .inr l => .inr (l,p.2)
  invFun p := match p with | .inl (l,w) => (.inl l,w) | .inr (l,w) => (.inr l,w)
  left_inv p := by rcases p with ⟨l,w⟩; cases l <;> rfl
  right_inv p := by cases p <;> rfl

/-- Only tuple regrouping and the fixed binary encoding of the four graph labels. -/
def labelLowerWiring (W : Type*) :
    (TransducerCompiler.GateSynthesis.Space (Fin 4) × W) ≃ Bool × ((Label × W) ⊕ (Label × W)) :=
  (Equiv.prodAssoc Bool LabelBits W).trans
    (Equiv.prodCongr (Equiv.refl Bool)
      ((Equiv.prodCongr labelWiring (Equiv.refl W)).trans (labelDistribution W)))

def borrow (U : Matrix.unitaryGroup W ℂ) : Matrix.unitaryGroup (Bool × W) ℂ :=
  tensorUnitary 1 U

@[simp] theorem borrow_mul (U V : Matrix.unitaryGroup W ℂ) : borrow (U*V) = borrow U*borrow V := by
  rw [borrow, borrow, borrow, tensorUnitary_mul, mul_one]

@[simp] theorem borrow_one : borrow (1 : Matrix.unitaryGroup W ℂ) = 1 := by
  apply Subtype.ext
  exact Matrix.one_kronecker_one

theorem label_borrow_place (U : Matrix.unitaryGroup LabelBits ℂ) :
    TransducerCompiler.GateSynthesis.placeHom (labelLowerWiring W)
      (TransducerCompiler.GateSynthesis.dataHom U) =
    borrow (TransducerCompiler.GateSynthesis.placeHom (labelDistribution W)
      (rewireUnitary labelWiring U)) := by
  apply Subtype.ext
  ext ⟨b,i⟩ ⟨r,j⟩
  rcases i with ⟨l,i⟩|⟨l,i⟩ <;> rcases j with ⟨m,j⟩|⟨m,j⟩ <;>
    simp [placeHom_entries, TransducerCompiler.GateSynthesis.dataHom,
      labelLowerWiring, labelDistribution, borrow, tensorUnitary,
      HadamardClock.tensorUnitary, rewireUnitary, Matrix.one_apply] <;>
    split_ifs <;> simp_all

theorem labelDistribution_left (U : Matrix.unitaryGroup Label ℂ) :
    TransducerCompiler.GateSynthesis.placeHom (labelDistribution W) (sumUnitary U 1) =
      sumUnitary (tensorUnitary U (1 : Matrix.unitaryGroup W ℂ)) 1 := by
  apply Subtype.ext
  ext i j
  rcases i with ⟨l,i⟩|⟨l,i⟩ <;> rcases j with ⟨m,j⟩|⟨m,j⟩ <;>
    simp [placeHom_entries, labelDistribution, sumUnitary, tensorUnitary,
      HadamardClock.tensorUnitary, Matrix.one_apply] <;>
    split_ifs <;> simp_all

theorem labelDistribution_right (U : Matrix.unitaryGroup Label ℂ) :
    TransducerCompiler.GateSynthesis.placeHom (labelDistribution W) (sumUnitary 1 U) =
      sumUnitary 1 (tensorUnitary U (1 : Matrix.unitaryGroup W ℂ)) := by
  apply Subtype.ext
  ext i j
  rcases i with ⟨l,i⟩|⟨l,i⟩ <;> rcases j with ⟨m,j⟩|⟨m,j⟩ <;>
    simp [placeHom_entries, labelDistribution, sumUnitary, tensorUnitary,
      HadamardClock.tensorUnitary, Matrix.one_apply] <;>
    split_ifs <;> simp_all

/-- A literal list of the verified real one/two-qubit instructions, with explicit spectators. -/
def labelLowerCircuit (W A B : Type*) [Fintype W] [DecidableEq W]
    (p : BinaryClock.Program (Fin 4)) :
    QueryCircuit A B (Bool × ((Label × W) ⊕ (Label × W))) :=
  (GateSynthesis.lowerProgram p).map (fun g =>
    .work (TransducerCompiler.GateSynthesis.placeHom (labelLowerWiring W) g.eval))

theorem labelLowerCircuit_eval (p : BinaryClock.Program (Fin 4))
    (U : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (labelLowerCircuit W A B p).eval U Ub =
      TransducerCompiler.GateSynthesis.placeHom (labelLowerWiring W)
        (TransducerCompiler.GateSynthesis.eval (GateSynthesis.lowerProgram p)) := by
  unfold labelLowerCircuit
  generalize GateSynthesis.lowerProgram p = l
  induction l with
  | nil => simp [QueryCircuit.eval, TransducerCompiler.GateSynthesis.eval]
  | cons g gs ih =>
    simp [QueryCircuit.eval, QueryInstruction.eval, TransducerCompiler.GateSynthesis.eval, ih, map_mul]

theorem label01Circuit_eval (U : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (labelLowerCircuit W A B label01Program).eval U Ub =
      borrow (sumUnitary (tensorUnitary (labelUnitary 1 (by decide)) (1 : Matrix.unitaryGroup W ℂ)) 1) := by
  rw [labelLowerCircuit_eval, GateSynthesis.lowerProgram_eq, label_borrow_place,
    label01Program_unitary, labelDistribution_left]

theorem label02Circuit_eval (U : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (labelLowerCircuit W A B label02Program).eval U Ub =
      borrow (sumUnitary 1 (tensorUnitary (labelUnitary 2 (by decide)) (1 : Matrix.unitaryGroup W ℂ))) := by
  rw [labelLowerCircuit_eval, GateSynthesis.lowerProgram_eq, label_borrow_place,
    label02Program_unitary, labelDistribution_right]

theorem labelLowerCircuit_counts (p : BinaryClock.Program (Fin 4)) :
    (labelLowerCircuit W A B p).matrixQueries=0 ∧
      (labelLowerCircuit W A B p).vectorQueries=0 ∧
      workInstructions (labelLowerCircuit W A B p)=(GateSynthesis.lowerProgram p).length := by
  unfold labelLowerCircuit
  generalize GateSynthesis.lowerProgram p = l
  induction l with
  | nil => simp [QueryCircuit.matrixQueries, QueryCircuit.vectorQueries, workInstructions]
  | cons g gs ih =>
    simpa [QueryCircuit.matrixQueries, QueryCircuit.vectorQueries, workInstructions] using ih

/-- Two Hadamards, one controlled X, and the same two original-oracle calls. -/
def controlledSignalCircuit (S D B : Type*) [Fintype S] [DecidableEq S]
    [Fintype D] [DecidableEq D] :
    QueryCircuit (S × D) B (Bool × (BranchSpace S D ⊕ BranchSpace S D)) :=
  (((signalCircuit (S × D) B).lift (tensorPort ((S × D) ⊕ (S × D)) Label)).lift
    (leftOraclePort (BranchSpace S D))).lift (tensorPort (BranchSpace S D ⊕ BranchSpace S D) Bool)

theorem controlledSignalCircuit_eval (U : Matrix.unitaryGroup (S × D) ℂ)
    (Ub : Matrix.unitaryGroup B ℂ) :
    (controlledSignalCircuit S D B).eval U Ub =
      borrow (sumUnitary (tensorUnitary (1 : Matrix.unitaryGroup Label ℂ) (hermitianSignal U)) 1) := by
  simp [controlledSignalCircuit, QueryCircuit.lift_eval, signalCircuit_eval,
    tensorPort_apply, leftOraclePort_apply, borrow]

/-- Every large reversible work instruction has been expanded to its actual
36- or34-gate elementary list. All remaining work instructions are the fixed
one- and two-qubit gates proved in SmallGates. -/
def realizedSelectCircuit (S D B : Type*) [Fintype S] [DecidableEq S]
    [Fintype D] [DecidableEq D] (κ : ℝ) (hκ : 0 < κ) :
    QueryCircuit (S × D) B (Bool × (BranchSpace S D ⊕ BranchSpace S D)) :=
  [.work (borrow (weightedMix (BranchSpace S D) κ hκ)⁻¹)] ++
  controlledSignalCircuit S D B ++
  labelLowerCircuit ((S × D) ⊕ (S × D)) (S × D) B label01Program ++
  [.work (borrow (sumUnitary (1 : Matrix.unitaryGroup (BranchSpace S D) ℂ) (-1)))] ++
  labelLowerCircuit ((S × D) ⊕ (S × D)) (S × D) B label02Program ++
  [.work (borrow (weightedMix (BranchSpace S D) κ hκ))]

theorem sumUnitary_mul (U V X Y : Matrix.unitaryGroup W ℂ) :
    sumUnitary U V * sumUnitary X Y = sumUnitary (U*X) (V*Y) := by
  apply Subtype.ext
  simp [sumUnitary, Matrix.fromBlocks_multiply]

theorem negativeBranch_factor :
    tensorUnitary (labelUnitary 2 (by decide)) (1 : Matrix.unitaryGroup ((S × D) ⊕ (S × D)) ℂ) * (-1) =
      branchI S D := by
  apply Subtype.ext
  change ((labelUnitary 2 (by decide)).val ⊗ₖ (1 : Matrix _ _ ℂ)) * (-(1 : Matrix _ _ ℂ)) =
    (-(labelUnitary 2 (by decide)).val) ⊗ₖ (1 : Matrix _ _ ℂ)
  simp only [Matrix.mul_neg, Matrix.mul_one]
  ext i j
  simp [Matrix.kronecker_apply]

theorem realizedSelectCircuit_eval (κ : ℝ) (hκ : 0 < κ)
    (U : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (realizedSelectCircuit S D B κ hκ).eval U Ub =
      borrow (weightedSelect κ hκ (branchA U) (branchI S D)) := by
  simp only [realizedSelectCircuit, QueryCircuit.eval_append, QueryCircuit.eval, QueryInstruction.eval,
    one_mul, controlledSignalCircuit_eval, label01Circuit_eval, label02Circuit_eval]
  rw [← borrow_mul, ← borrow_mul, ← borrow_mul, ← borrow_mul, ← borrow_mul]
  congr 1
  try simp only [mul_assoc]
  rw [← mul_assoc (sumUnitary 1 _) (sumUnitary 1 _) _, sumUnitary_mul,
    mul_one, negativeBranch_factor]
  rw [← mul_assoc (sumUnitary _ 1) (sumUnitary _ 1) _, sumUnitary_mul,
    mul_one, tensorUnitary_mul, mul_one, one_mul]
  change _ = weightedSelect κ hκ (branchA U) (branchI S D)
  rw [← mul_assoc (sumUnitary 1 _) (sumUnitary _ 1) _, sumUnitary_right_left]
  simp [weightedSelect, branchA, mul_assoc]


theorem workInstructions_append (c d : QueryCircuit A B W) :
    workInstructions (c++d) = workInstructions c + workInstructions d := by
  induction c with
  | nil => simp [workInstructions]
  | cons g gs ih => cases g <;> simp [workInstructions, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem workInstructions_lift {V : Type*} [Fintype V] [DecidableEq V]
    (p : QueryPort W V) (c : QueryCircuit A B W) :
    workInstructions (c.lift p) = workInstructions c := by
  induction c with
  | nil => rfl
  | cons g gs ih => cases g <;> simp [QueryCircuit.lift, QueryInstruction.lift, workInstructions] at ih ⊢ <;> exact ih

theorem controlledSignalCircuit_counts :
    (controlledSignalCircuit S D B).matrixQueries=2 ∧
      (controlledSignalCircuit S D B).vectorQueries=0 ∧
      workInstructions (controlledSignalCircuit S D B)=3 := by
  simp [controlledSignalCircuit, (QueryCircuit.lift_counts _ _).1,
    (QueryCircuit.lift_counts _ _).2, workInstructions_lift,
    signalCircuit_counts.1, signalCircuit_counts.2.1, signalCircuit_counts.2.2]

/-- Exactly76 actual elementary work instructions and exactly two input matrix calls. -/
theorem realizedSelectCircuit_counts (κ : ℝ) (hκ : 0 < κ) :
    (realizedSelectCircuit S D B κ hκ).matrixQueries=2 ∧
      (realizedSelectCircuit S D B κ hκ).vectorQueries=0 ∧
      workInstructions (realizedSelectCircuit S D B κ hκ)=76 := by
  simp [realizedSelectCircuit, QueryCircuit.matrixQueries_append,
    QueryCircuit.vectorQueries_append, workInstructions_append,
    controlledSignalCircuit_counts.1, controlledSignalCircuit_counts.2.1,
    controlledSignalCircuit_counts.2.2, (labelLowerCircuit_counts _).1,
    (labelLowerCircuit_counts _).2.1, (labelLowerCircuit_counts _).2.2,
    QueryCircuit.matrixQueries, QueryCircuit.vectorQueries, workInstructions,
    label_gate_counts.1, label_gate_counts.2]

end OptimalQLS.GraphEncoding
