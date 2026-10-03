import OptimalQLS.Refinement.PhysicalProgram.Flags
import OptimalQLS.Refinement.PhysicalProgram.Correctness

/-! # Complete coherent physical run with one fixed set of emitted witnesses -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open scoped Classical Matrix.Norms.L2Operator
namespace OptimalQLS.Refinement.PhysicalProgram
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform PhysicalPadding

variable {a n : ℕ} {κ s ŝ ε : ℝ} {h : BudgetParameters κ s ŝ}

def Implementation.circuit (I : Implementation a n (ε := ε) h) : Circuit a n (preparationExponent κ) :=
  program a n _ I.preparation I.filter I.correction

def Implementation.accepted (I : Implementation a n (ε := ε) h)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    EuclideanSpace ℂ (Bits n) :=
  acceptedVector a n _ (CompilerAttachment.preparationExponent_pos h) I.preparation I.filter I.correction UA Ub

theorem Implementation.singleControlled (I : Implementation a n (ε := ε) h) :
    SingleControlled I.circuit :=
  program_single_controlled a n _ I.preparation I.preparation_strict I.filter I.filter_ports I.filter_vector
    I.correction I.correction_ports I.correction_vector

theorem Implementation.exact_counts (I : Implementation a n (ε := ε) h) :
    (I.circuit.toQuery (gateEval a n _ (CompilerAttachment.preparationExponent_pos h))).matrixQueries=
      2*mainBudget κ+(I.filter.toQuery (GraphAttachedGate.eval a)).matrixQueries+
        (I.correction.toQuery (SingleFlagGate.eval a)).matrixQueries ∧
    (I.circuit.toQuery (gateEval a n _ (CompilerAttachment.preparationExponent_pos h))).vectorQueries=
      2*reflectionBudget κ ŝ+1 ∧
    I.circuit.workGates=I.preparation.workGates+I.filter.workGates+I.correction.workGates := by
  have hc := program_counts a n _ (CompilerAttachment.preparationExponent_pos h) I.preparation I.filter I.correction
  rw [I.preparation_matrix,I.preparation_vector,I.filter_vector,I.correction_vector] at hc
  simpa only [Nat.add_zero] using hc

theorem Implementation.work_bound (I : Implementation a n (ε := ε) h) :
    (I.circuit.workGates : ℝ)<200000000000000*κ*(a+1)+700000000000*(κ/s)*(n+1)+
      3341621776*κ*(a+1)*Real.log (1/(ε/1024)) := by
  have hp := CompilerAttachment.actual_gate_bound a n _ h I.preparation_gates
  rw [I.exact_counts.2.2]
  push_cast
  nlinarith [I.filter_gates,I.correction_gates]

theorem Implementation.matrix_bound (I : Implementation a n (ε := ε) h) :
    ((I.circuit.toQuery (gateEval a n _ (CompilerAttachment.preparationExponent_pos h))).matrixQueries : ℝ)<
      512000000*κ+840096*κ*Real.log (1/(ε/1024)) := by
  rw [I.exact_counts.1]
  push_cast
  linarith [h.mainBudget_bounds.2,I.filter_matrix,I.correction_matrix]

/-- Correctness is uniform over arbitrary active computational embeddings, including
noncontiguous dilation ranges. The full physical UA and Ub remain untouched. -/
theorem Implementation.correctness (I : Implementation a n (ε := ε) h)
    {D : Type*} [Fintype D] [DecidableEq D] (f : D ↪ Bits n)
    (A : Matrix D D ℂ) (hA : A.IsHermitian) (hunit : IsUnit A)
    (hinv : ‖Ring.inverse A‖≤κ) (hε0 : 0<ε) (hε1 : ε<1/2)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (henc : IsBlockEncoding (fun _ : Fin a=>false) 1 0 UA (zeroExtend f A))
    (Ub : Matrix.unitaryGroup (Bits n) ℂ) (b : EuclideanSpace ℂ D) (hb : ‖b‖=1)
    (hcol : ∀ i,Ub i (fun _ : Fin n=>false)=coordinateIsometry f b i)
    (hs : s=solutionScale 1 A b) :
    I.accepted UA Ub≠0 ∧
      ‖NormedSpace.normalize (I.accepted UA Ub)-coordinateIsometry f
        (NormedSpace.normalize (Ring.inverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) b))‖≤ε/2 ∧
      1/65536<‖I.accepted UA Ub‖^2 := by
  exact program_correctness a n f h I.preparation I.filter I.correction I.preparation_state
    A hA hunit hinv hε0 hε1 UA henc Ub b hb hcol hs
    (I.filter_block UA Ub _ (zeroExtend_hermitian f A hA) henc)
    (I.correction_block UA Ub _ (zeroExtend_hermitian f A hA) henc)

theorem Implementation.output_norm (I : Implementation a n (ε := ε) h)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    ‖WithLp.toLp 2 (((I.circuit.toQuery (gateEval a n _ (CompilerAttachment.preparationExponent_pos h))).eval UA Ub).val*ᵥ
      Pi.single (initial a n (preparationExponent κ)) 1)‖=1 := by
  have hn := unitary_norm ((I.circuit.toQuery (gateEval a n _ (CompilerAttachment.preparationExponent_pos h))).eval UA Ub)
    (WithLp.toLp 2 (Pi.single (initial a n (preparationExponent κ)) (1:ℂ)))
  have hzero : ‖WithLp.toLp 2 (Pi.single (initial a n (preparationExponent κ)) (1:ℂ) : Register a n (preparationExponent κ)→ℂ)‖=1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1)).mp
    simp [EuclideanSpace.norm_sq_eq,Pi.single_apply,apply_ite]
  exact hn.trans hzero

theorem Implementation.probability_le_one (I : Implementation a n (ε := ε) h)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    ‖I.accepted UA Ub‖^2≤1 := by
  have hn := accepted_norm_le (prepZero a (preparationExponent κ)) (physicalZero (a+4)) (physicalZero a)
    (((I.circuit.toQuery (gateEval a n _ (CompilerAttachment.preparationExponent_pos h))).eval UA Ub).val*ᵥ
      Pi.single (initial a n (preparationExponent κ)) 1)
  rw [I.output_norm UA Ub] at hn
  have he : ‖I.accepted UA Ub‖≤1 := hn
  nlinarith [norm_nonneg (I.accepted UA Ub)]

/-- One finite actual program is chosen before all oracle matrices and all active
embeddings. Its attached work leaves, both oracle roles, and dimensions are physical. -/
theorem physical_run_complete (a n : ℕ) {κ s ŝ ε : ℝ} (h : BudgetParameters κ s ŝ)
    (hε0 : 0<ε) (hε1 : ε<1/2) :
    ∃ I : Implementation a n (ε := ε) h,
      SingleControlled I.circuit ∧
      (∀ g,NamedInstruction.gate g∈I.circuit → g.arity≤2) ∧
      (I.circuit.toQuery (gateEval a n _ (CompilerAttachment.preparationExponent_pos h))).matrixQueries=
        2*mainBudget κ+(I.filter.toQuery (GraphAttachedGate.eval a)).matrixQueries+
          (I.correction.toQuery (SingleFlagGate.eval a)).matrixQueries ∧
      (I.circuit.toQuery (gateEval a n _ (CompilerAttachment.preparationExponent_pos h))).vectorQueries=
        2*reflectionBudget κ ŝ+1 ∧
      I.circuit.workGates=I.preparation.workGates+I.filter.workGates+I.correction.workGates ∧
      Fintype.card (Register a n (preparationExponent κ))=2^(n+3*a+2*preparationExponent κ+27) := by
  obtain ⟨I⟩ := implementation_exists a n h hε0 hε1
  exact ⟨I,I.singleControlled,fun g _=>Gate.arity_le_two g,I.exact_counts.1,I.exact_counts.2.1,
    I.exact_counts.2.2,register_card a n _⟩

end OptimalQLS.Refinement.PhysicalProgram
