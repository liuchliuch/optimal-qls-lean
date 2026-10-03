import OptimalQLS.Refinement.PhysicalProgram.Uniform

/-! # One physical code witness before the hidden exact solution scale

Changing the proof-only scale parameter retains all three instruction lists
literally. Only semantic and numerical proofs are transported.
-/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open scoped Classical Matrix.Norms.L2Operator
namespace OptimalQLS.Refinement.PhysicalProgram
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform PhysicalPadding
variable {a n : ℕ} {κ s ŝ ε : ℝ} {h : BudgetParameters κ s ŝ}

def Implementation.forScale (I : Implementation a n (ε := ε) h) {t : ℝ}
    (h' : BudgetParameters κ t ŝ) : Implementation a n (ε := ε) h' where
  preparation := I.preparation
  filter := I.filter
  correction := I.correction
  preparation_strict := I.preparation_strict
  preparation_matrix := I.preparation_matrix
  preparation_vector := I.preparation_vector
  preparation_gates := I.preparation_gates
  preparation_state := by
    intro UA Ub
    rw [←CompilerAttachment.originalPreparedState_uniform a n h h' UA Ub]
    exact I.preparation_state UA Ub
  filter_matrix := I.filter_matrix
  filter_vector := I.filter_vector
  filter_gates := I.filter_gates
  filter_ports := I.filter_ports
  filter_block := I.filter_block
  correction_matrix := I.correction_matrix
  correction_vector := I.correction_vector
  correction_gates := I.correction_gates
  correction_ports := I.correction_ports
  correction_block := I.correction_block

@[simp] theorem Implementation.forScale_preparation (I : Implementation a n (ε := ε) h) {t : ℝ}
    (h' : BudgetParameters κ t ŝ) : (I.forScale h').preparation=I.preparation := rfl
@[simp] theorem Implementation.forScale_filter (I : Implementation a n (ε := ε) h) {t : ℝ}
    (h' : BudgetParameters κ t ŝ) : (I.forScale h').filter=I.filter := rfl
@[simp] theorem Implementation.forScale_correction (I : Implementation a n (ε := ε) h) {t : ℝ}
    (h' : BudgetParameters κ t ŝ) : (I.forScale h').correction=I.correction := rfl

/-- Literal list equality, not merely equality of costs or successful branches. -/
@[simp] theorem Implementation.forScale_circuit (I : Implementation a n (ε := ε) h) {t : ℝ}
    (h' : BudgetParameters κ t ŝ) : (I.forScale h').circuit=I.circuit := rfl

@[simp] theorem Implementation.forScale_accepted (I : Implementation a n (ε := ε) h) {t : ℝ}
    (h' : BudgetParameters κ t ŝ)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    (I.forScale h').accepted UA Ub=I.accepted UA Ub := rfl

/-- The same emitted code admits the stronger bound for each actual hidden scale. -/
theorem Implementation.work_bound_uniform (I : Implementation a n (ε := ε) h) {t : ℝ}
    (h' : BudgetParameters κ t ŝ) :
    (I.circuit.workGates : ℝ)<200000000000000*κ*(a+1)+700000000000*(κ/t)*(n+1)+
      3341621776*κ*(a+1)*Real.log (1/(ε/1024)) := by
  exact (I.forScale h').work_bound

/-- All operator/source promises are quantified after one chosen physical circuit. -/
theorem Implementation.correctness_uniform (I : Implementation a n (ε := ε) h) {t : ℝ}
    (h' : BudgetParameters κ t ŝ) {D : Type*} [Fintype D] [DecidableEq D]
    (f : D ↪ Bits n) (A : Matrix D D ℂ) (hA : A.IsHermitian) (hunit : IsUnit A)
    (hinv : ‖Ring.inverse A‖≤κ) (hε0 : 0<ε) (hε1 : ε<1/2)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (henc : IsBlockEncoding (fun _ : Fin a=>false) 1 0 UA (zeroExtend f A))
    (Ub : Matrix.unitaryGroup (Bits n) ℂ) (b : EuclideanSpace ℂ D) (hb : ‖b‖=1)
    (hcol : ∀ i,Ub i (fun _ : Fin n=>false)=coordinateIsometry f b i)
    (ht : t=solutionScale 1 A b) :
    I.accepted UA Ub≠0 ∧
      ‖NormedSpace.normalize (I.accepted UA Ub)-coordinateIsometry f
        (NormedSpace.normalize (Ring.inverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) b))‖≤ε/2 ∧
      1/65536<‖I.accepted UA Ub‖^2 := by
  exact (I.forScale h').correctness f A hA hunit hinv hε0 hε1 UA henc Ub b hb hcol ht

/-- Closed synthesis before every admissible hidden scale and active embedding. -/
theorem physical_run_scale_uniform (a n : ℕ) {κ s ŝ ε : ℝ} (h : BudgetParameters κ s ŝ)
    (hε0 : 0<ε) (hε1 : ε<1/2) :
    ∃ I : Implementation a n (ε := ε) h,
      SingleControlled I.circuit ∧ ∀ (t : ℝ) (h' : BudgetParameters κ t ŝ),
        (I.forScale h').circuit=I.circuit ∧ UniformCorrect (I.forScale h') ∧
        (I.circuit.workGates : ℝ)<200000000000000*κ*(a+1)+700000000000*(κ/t)*(n+1)+
          3341621776*κ*(a+1)*Real.log (1/(ε/1024)) := by
  obtain ⟨I⟩ := implementation_exists a n h hε0 hε1
  refine ⟨I,I.singleControlled,?_⟩
  intro t h'
  refine ⟨rfl,?_,I.work_bound_uniform h'⟩
  intro D _ _ f A hA hu hi UA henc Ub b hb hcol ht
  exact (I.forScale h').correctness f A hA hu hi hε0 hε1 UA henc Ub b hb hcol ht

end OptimalQLS.Refinement.PhysicalProgram
