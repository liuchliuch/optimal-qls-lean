import OptimalQLS.Reduction.GenericSolver.PhysicalFrames

/-! Actual original-oracle macros for arbitrary physically placed calls and
arbitrary supplied local work gates. Clean scratch is restored coherently. -/
noncomputable section
open scoped Classical
namespace OptimalQLS.Reduction.GenericSolver.Physical
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla LowerBounds
open Refinement.CostedExecution Preparation.CompilerAttachment
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
variable {P W : Type} [Fintype P] [DecidableEq P]
  {chart : P ≃ (W → Bool)} {a n : ℕ}

inductive Gate (chart : P ≃ (W → Bool)) (a n : ℕ) where
  | old (g : TransducerCompiler.Physical.LocalGate chart)
  | matrix (F : MatrixFrame chart a n) (g : PhaseGate DilationWire)
  | vector (F : VectorFrame chart n) (g : PhaseGate DilationWire)

def gateEval : Gate chart a n → Matrix.unitaryGroup (P × PhaseScratch) ℂ
  | .old g => (scratchPort (Equiv.refl _)).apply g.eval
  | .matrix F g => GateSynthesis.placeHom (matrixWiring a n F.frame) (elementaryPlacement g.eval)
  | .vector F g => GateSynthesis.placeHom (vectorWiring n F.frame) (elementaryPlacement g.eval)

abbrev Circuit (chart : P ≃ (W → Bool)) (a n : ℕ) :=
  NamedCircuit (Gate chart a n) (Bits a × Bits n) (Bits n) (P × PhaseScratch)

def matrixCode (F : MatrixFrame chart a n) (adj : Bool) : Circuit chart a n :=
  attachList (matrixWiring a n F.frame) (Gate.matrix F) (dilationOracleCircuit adj)
def vectorCode (F : VectorFrame chart n) (adj : Bool) : Circuit chart a n :=
  attachList (vectorWiring n F.frame) (Gate.vector F) (vectorDilationCircuit adj)

theorem gate_local (g : Gate chart a n) : IsTwoLocal (coordinates chart) (gateEval g) := by
  cases g with
  | old g =>
    rw [gateEval,scratchPort_apply]
    exact IsTwoLocal.place _ oldEmbedding _ g.local
  | matrix F g =>
    exact IsTwoLocal.place _ F.wires _
      (IsTwoLocal.place _ (phaseMatrixEmbedding a n) _ (phase_leaf_local g))
  | vector F g =>
    exact IsTwoLocal.place _ F.wires _
      (IsTwoLocal.place _ (phaseVectorEmbedding n) _ (phase_leaf_local g))

theorem matrixCode_counts (F : MatrixFrame chart a n) (adj : Bool) :
    ((matrixCode F adj).toQuery gateEval).matrixQueries=2 ∧
    ((matrixCode F adj).toQuery gateEval).vectorQueries=0 ∧
    (matrixCode F adj).workGates≤4801 := by
  rw [matrixCode,attachList_toQuery _ (Gate.matrix F) gateEval (fun _=>rfl)]
  exact ⟨(QueryCircuit.lift_counts _ _).1.trans (dilationOracleCircuit_counts adj).1,
    (QueryCircuit.lift_counts _ _).2.trans (dilationOracleCircuit_counts adj).2.1,
    by rw [attachList_workGates]; exact (dilationOracleCircuit_counts adj).2.2⟩

theorem vectorCode_counts (F : VectorFrame chart n) (adj : Bool) :
    ((vectorCode (a := a) F adj).toQuery gateEval).matrixQueries=0 ∧
    ((vectorCode (a := a) F adj).toQuery gateEval).vectorQueries=1 ∧
    (vectorCode (a := a) F adj).workGates=0 := by
  rw [vectorCode,attachList_toQuery _ (Gate.vector F) gateEval (fun _=>rfl)]
  exact ⟨(QueryCircuit.lift_counts _ _).1.trans (vectorDilationCircuit_counts adj).1,
    (QueryCircuit.lift_counts _ _).2.trans (vectorDilationCircuit_counts adj).2.1,
    by rw [attachList_workGates]; exact (vectorDilationCircuit_counts adj).2.2⟩

theorem matrixCode_intertwines (F : MatrixFrame chart a n) (adj : Bool)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    (((matrixCode F adj).toQuery gateEval).eval UA Ub).val * basisInsertion clean =
      basisInsertion clean * (F.port.apply (if adj then (dilationEncoding UA)⁻¹ else dilationEncoding UA)).val := by
  rw [matrixCode,attachList_eval _ (Gate.matrix F) gateEval (fun _=>rfl)]
  have ht := tensor_intertwines (D := F.Rest) dilationSignalClean _ _
    (dilationEncodingCircuit_intertwines adj UA Ub)
  have he := clean_intertwines_transport (matrixWiring a n F.frame) F.frame
    (fun x=>(dilationSignalClean x.1,x.2)) _ _ ht
  have hc : (fun x => matrixWiring a n F.frame
      (dilationSignalClean ((F.frame.symm x).1),(F.frame.symm x).2))=clean := by
    funext x
    simp [matrixWiring,scratchFrame,clean]
  rw [hc] at he
  rw [MatrixFrame.port_apply]
  exact he

theorem vectorCode_intertwines (F : VectorFrame chart n) (adj : Bool)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    (((vectorCode F adj).toQuery gateEval).eval UA Ub).val * basisInsertion clean =
      basisInsertion clean * (F.port.apply (if adj then (preparation Ub)⁻¹ else preparation Ub)).val := by
  rw [vectorCode,attachList_eval _ (Gate.vector F) gateEval (fun _=>rfl)]
  have ht := tensor_intertwines (D := F.Rest) dilationSumClean _ _
    (preparationCircuit_intertwines adj UA Ub)
  have he := clean_intertwines_transport (vectorWiring n F.frame) F.frame
    (fun x=>(dilationSumClean x.1,x.2)) _ _ ht
  have hc : (fun x => vectorWiring n F.frame
      (dilationSumClean ((F.frame.symm x).1),(F.frame.symm x).2))=clean := by
    funext x
    simp [vectorWiring,scratchFrame,clean]
  rw [hc] at he
  rw [VectorFrame.port_apply]
  exact he

end OptimalQLS.Reduction.GenericSolver.Physical
