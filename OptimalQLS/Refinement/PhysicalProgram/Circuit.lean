import OptimalQLS.Refinement.PhysicalProgram.Placement

/-! # Literal full-run work gates and exactly additive emitted resources -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.Refinement.PhysicalProgram
open Matrix TransducerCompiler BinaryClock PolynomialTransform

inductive Gate (a n ℓ : ℕ) where
  | preparation (g : Preparation.CompilerAttachment.Gate a n ℓ)
  | filter (g : GraphAttachedGate a)
  | correction (g : SingleFlagGate a)

def gateEval (a n ℓ : ℕ) (hℓ : 0<ℓ) : Gate a n ℓ → Matrix.unitaryGroup (Register a n ℓ) ℂ
  | .preparation g => (preparationPort a n ℓ).apply (Preparation.CompilerAttachment.gateEval a n ℓ hℓ g)
  | .filter g => filterPort.apply (GraphAttachedGate.eval a g)
  | .correction g => correctionPort.apply (SingleFlagGate.eval a g)

def Gate.arity {a n ℓ : ℕ} : Gate a n ℓ → ℕ
  | .preparation g => g.arity
  | .filter g => g.arity
  | .correction g => g.arity

theorem Gate.arity_le_two {a n ℓ : ℕ} (g : Gate a n ℓ) : g.arity≤2 := by
  cases g with
  | preparation g => exact Preparation.CompilerAttachment.Gate.arity_le_two _
  | filter g => exact GraphAttachedGate.arity_le_two _
  | correction g => exact SingleFlagGate.arity_le_two _

abbrev Circuit (a n ℓ : ℕ) :=
  NamedCircuit (Gate a n ℓ) (Bits a × Bits n) (Bits n) (Register a n ℓ)

def program (a n ℓ : ℕ) (cp : Preparation.CompilerAttachment.Circuit a n ℓ)
    (cf : GraphAttachedCircuit a (Bits n) (Bits n))
    (cc : SingleFlagCircuit a (Bits n) (Bits n)) : Circuit a n ℓ :=
  liftList (preparationPort a n ℓ) Gate.preparation cp ++
    liftList filterPort Gate.filter cf ++ liftList correctionPort Gate.correction cc

theorem program_toQuery (a n ℓ : ℕ) (hℓ : 0<ℓ)
    (cp : Preparation.CompilerAttachment.Circuit a n ℓ)
    (cf : GraphAttachedCircuit a (Bits n) (Bits n))
    (cc : SingleFlagCircuit a (Bits n) (Bits n)) :
    (program a n ℓ cp cf cc).toQuery (gateEval a n ℓ hℓ)=
      (cp.toQuery (Preparation.CompilerAttachment.gateEval a n ℓ hℓ)).lift (preparationPort a n ℓ) ++
        refinementProgram (cf.toQuery (GraphAttachedGate.eval a)) (cc.toQuery (SingleFlagGate.eval a)) := by
  simp only [program,NamedCircuit.toQuery_append]
  rw [liftList_toQuery (preparationPort a n ℓ) Gate.preparation
      (Preparation.CompilerAttachment.gateEval a n ℓ hℓ) (gateEval a n ℓ hℓ) (fun _=>rfl),
    liftList_toQuery filterPort Gate.filter (GraphAttachedGate.eval a) (gateEval a n ℓ hℓ) (fun _=>rfl),
    liftList_toQuery correctionPort Gate.correction (SingleFlagGate.eval a) (gateEval a n ℓ hℓ) (fun _=>rfl)]
  simp only [refinementProgram,List.append_assoc]

theorem program_counts (a n ℓ : ℕ) (hℓ : 0<ℓ)
    (cp : Preparation.CompilerAttachment.Circuit a n ℓ)
    (cf : GraphAttachedCircuit a (Bits n) (Bits n))
    (cc : SingleFlagCircuit a (Bits n) (Bits n)) :
    ((program a n ℓ cp cf cc).toQuery (gateEval a n ℓ hℓ)).matrixQueries=
      (cp.toQuery (Preparation.CompilerAttachment.gateEval a n ℓ hℓ)).matrixQueries+
      (cf.toQuery (GraphAttachedGate.eval a)).matrixQueries+(cc.toQuery (SingleFlagGate.eval a)).matrixQueries ∧
    ((program a n ℓ cp cf cc).toQuery (gateEval a n ℓ hℓ)).vectorQueries=
      (cp.toQuery (Preparation.CompilerAttachment.gateEval a n ℓ hℓ)).vectorQueries+
      (cf.toQuery (GraphAttachedGate.eval a)).vectorQueries+(cc.toQuery (SingleFlagGate.eval a)).vectorQueries ∧
    (program a n ℓ cp cf cc).workGates=cp.workGates+cf.workGates+cc.workGates := by
  constructor
  · rw [program_toQuery,QueryCircuit.matrixQueries_append,(QueryCircuit.lift_counts _ _).1,
      (refinementProgram_counts _ _).1]
    omega
  constructor
  · rw [program_toQuery,QueryCircuit.vectorQueries_append,(QueryCircuit.lift_counts _ _).2,
      (refinementProgram_counts _ _).2]
    omega
  · simp only [program,NamedCircuit.workGates_append,liftList_gates]

end OptimalQLS.Refinement.PhysicalProgram
