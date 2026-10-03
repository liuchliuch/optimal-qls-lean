import OptimalQLS.PhysicalRobustness.PhysicalProgram.Selection

/-! The literal noisy run, its Born branch, and exactly additive resources. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open scoped Classical Matrix.Norms.L2Operator
namespace OptimalQLS.PhysicalRobustness.PhysicalProgram
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform PhysicalPadding Refinement
open Refinement.PhysicalProgram
variable {a n : ℕ} {κ ŝ ε : ℝ}

def Implementation.budget (I : Implementation a n κ ŝ ε) :=
  selectionBudget I.kappa_ge_two I.estimate_lower I.estimate_upper

def Implementation.circuit (I : Implementation a n κ ŝ ε) :
    Refinement.PhysicalProgram.Circuit a n (preparationExponent (2*κ)) :=
  program a n _ I.preparation I.filter I.correction

def Implementation.accepted (I : Implementation a n κ ŝ ε)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    EuclideanSpace ℂ (Bits n) :=
  acceptedVector a n _ (CompilerAttachment.preparationExponent_pos I.budget)
    I.preparation I.filter I.correction UA Ub

theorem Implementation.singleControlled (I : Implementation a n κ ŝ ε) :
    SingleControlled I.circuit :=
  program_single_controlled a n _ I.preparation I.preparation_strict I.filter I.filter_ports I.filter_vector
    I.correction I.correction_ports I.correction_vector

theorem Implementation.exact_counts (I : Implementation a n κ ŝ ε) :
    (I.circuit.toQuery (gateEval a n _ (CompilerAttachment.preparationExponent_pos I.budget))).matrixQueries=
      2*mainBudget (2*κ)+(I.filter.toQuery (GraphAttachedGate.eval a)).matrixQueries+
        (I.correction.toQuery (SingleFlagGate.eval a)).matrixQueries ∧
    (I.circuit.toQuery (gateEval a n _ (CompilerAttachment.preparationExponent_pos I.budget))).vectorQueries=
      2*reflectionBudget (2*κ) (9*ŝ/8)+1 ∧
    I.circuit.workGates=I.preparation.workGates+I.filter.workGates+I.correction.workGates := by
  have hc := program_counts a n _ (CompilerAttachment.preparationExponent_pos I.budget)
    I.preparation I.filter I.correction
  rw [I.preparation_matrix,I.preparation_vector,I.filter_vector,I.correction_vector] at hc
  simpa only [Nat.add_zero] using hc

theorem Implementation.work_bound_uniform (I : Implementation a n κ ŝ ε)
    {t : ℝ} (h : BudgetParameters (2*κ) t (9*ŝ/8)) :
    (I.circuit.workGates : ℝ)<400000000000000*κ*(a+1)+700000000000*((2*κ)/t)*(n+1)+
      150000027051856*κ*(a+1)*Real.log (1/(ε/4096)) := by
  have hp := CompilerAttachment.actual_gate_bound a n _ h I.preparation_gates
  rw [I.exact_counts.2.2]
  push_cast
  nlinarith [I.filter_gates,I.correction_gates]

theorem Implementation.matrix_bound (I : Implementation a n κ ŝ ε) :
    ((I.circuit.toQuery (gateEval a n _ (CompilerAttachment.preparationExponent_pos I.budget))).matrixQueries : ℝ)<
      1024000000*κ+34004000192*κ*Real.log (1/(ε/4096)) := by
  rw [I.exact_counts.1]
  push_cast
  linarith [I.budget.mainBudget_bounds.2,I.filter_matrix,I.correction_matrix]

theorem Implementation.output_norm (I : Implementation a n κ ŝ ε)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    ‖WithLp.toLp 2 (((I.circuit.toQuery (gateEval a n _ (CompilerAttachment.preparationExponent_pos I.budget))).eval UA Ub).val*ᵥ
      Pi.single (initial a n (preparationExponent (2*κ))) 1)‖=1 := by
  have hn := unitary_norm ((I.circuit.toQuery (gateEval a n _ (CompilerAttachment.preparationExponent_pos I.budget))).eval UA Ub)
    (WithLp.toLp 2 (Pi.single (initial a n (preparationExponent (2*κ))) (1:ℂ)))
  have hzero : ‖WithLp.toLp 2 (Pi.single (initial a n (preparationExponent (2*κ))) (1:ℂ) :
      Register a n (preparationExponent (2*κ))→ℂ)‖=1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1)).mp
    simp
  exact hn.trans hzero

theorem Implementation.probability_le_one (I : Implementation a n κ ŝ ε)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    ‖I.accepted UA Ub‖^2≤1 := by
  have hn := accepted_norm_le (prepZero a (preparationExponent (2*κ))) (physicalZero (a+4)) (physicalZero a)
    (((I.circuit.toQuery (gateEval a n _ (CompilerAttachment.preparationExponent_pos I.budget))).eval UA Ub).val*ᵥ
      Pi.single (initial a n (preparationExponent (2*κ))) 1)
  rw [I.output_norm UA Ub] at hn
  have he : ‖I.accepted UA Ub‖≤1 := hn
  nlinarith [norm_nonneg (I.accepted UA Ub)]

/-- Total list length is exactly the number of emitted work leaves plus both
oracle-call counts. In particular the gate bound is attached to this list. -/
theorem named_length {G A W P : Type*} [Fintype A] [DecidableEq A]
    [Fintype W] [DecidableEq W] [Fintype P] [DecidableEq P]
    (e : G → Matrix.unitaryGroup P ℂ) (c : NamedCircuit G A W P) :
    c.length=c.workGates+(c.toQuery e).matrixQueries+(c.toQuery e).vectorQueries := by
  induction c with
  | nil => rfl
  | cons g c ih =>
    cases g <;> simp_all [NamedCircuit.toQuery,NamedInstruction.toQuery,NamedCircuit.workGates,
      QueryCircuit.matrixQueries,QueryCircuit.vectorQueries] <;> omega

theorem Implementation.length_eq (I : Implementation a n κ ŝ ε) :
    I.circuit.length=I.preparation.workGates+I.filter.workGates+I.correction.workGates+
      (2*mainBudget (2*κ)+(I.filter.toQuery (GraphAttachedGate.eval a)).matrixQueries+
        (I.correction.toQuery (SingleFlagGate.eval a)).matrixQueries)+
      (2*reflectionBudget (2*κ) (9*ŝ/8)+1) := by
  rw [named_length (gateEval a n _ (CompilerAttachment.preparationExponent_pos I.budget)),
    I.exact_counts.1,I.exact_counts.2.1,I.exact_counts.2.2]

end OptimalQLS.PhysicalRobustness.PhysicalProgram
