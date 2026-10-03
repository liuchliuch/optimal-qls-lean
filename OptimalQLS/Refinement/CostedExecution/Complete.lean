import OptimalQLS.Refinement.CostedExecution.Channels
import OptimalQLS.Refinement.CostedExecution.PhysicalProvenance
import OptimalQLS.Refinement.CostedExecution.ResourceAttachment

/-! Complete attachment of physical gate costs, exact resources and state
semantics to one and the same normalized QLSA primitive execution. -/
noncomputable section
namespace OptimalQLS.Refinement.CostedExecution
open Matrix LowerBounds PolynomialTransform Preparation PhysicalPadding TransducerCompiler BinaryClock
open scoped Matrix.Norms.L2Operator
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 16384
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
attribute [local irreducible] repeated Program.lower Repetition.repeatProgram
variable {a n : ℕ} {κ s ŝ ε : ℝ} {h : BudgetParameters κ s ŝ}

theorem successProbability_refines (I : PhysicalProgram.Implementation a n (ε:=ε) h)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (v : Fin (Fintype.card (PhysicalProgram.Register a n (preparationExponent κ))) → ℂ) :
    (physicalLower I 72000).successProbability UA Ub v=
      (PhysicalExecution.execution I).successProbability UA Ub v := by
  unfold FiniteOracleProgram.successProbability
  rw [execution_refines]

theorem conditionalOutput_refines (I : PhysicalProgram.Implementation a n (ε:=ε) h)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (v : Fin (Fintype.card (PhysicalProgram.Register a n (preparationExponent κ))) → ℂ) :
    (physicalLower I 72000).conditionalOutput UA Ub v=
      (PhysicalExecution.execution I).conditionalOutput UA Ub v := by
  unfold FiniteOracleProgram.conditionalOutput
  rw [successProbability_refines,execution_refines]

/-- The physical primitive execution inherits the already proved normalized
QLSA correctness, uniformly over all admissible hidden scales and embeddings. -/
theorem physical_execution_correct (I : PhysicalProgram.Implementation a n (ε:=ε) h)
    {t : ℝ} (h' : BudgetParameters κ t ŝ) {D : Type*} [Fintype D] [DecidableEq D]
    (f : D ↪ Bits n) (A : Matrix D D ℂ) (hA : A.IsHermitian) (hunit : IsUnit A)
    (hinv : ‖Ring.inverse A‖≤κ) (hε0 : 0<ε) (hε1 : ε<1/2)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (henc : IsBlockEncoding (fun _ : Fin a=>false) 1 0 UA (zeroExtend f A))
    (Ub : Matrix.unitaryGroup (Bits n) ℂ) (b : EuclideanSpace ℂ D) (hb : ‖b‖=1)
    (hcol : ∀ i,Ub i (fun _ : Fin n=>false)=coordinateIsometry f b i)
    (ht : t=solutionScale 1 A b) :
    (2 : ℝ)/3<(physicalLower I 72000).successProbability UA Ub
      (Repetition.basis (PhysicalExecution.initialIndex a n (preparationExponent κ))) ∧
    ∃ x : EuclideanSpace ℂ (Fin (2^n)), ‖x‖=1 ∧
      ‖x-PhysicalExecution.outputCoordinates n (coordinateIsometry f
        (NormedSpace.normalize (Ring.inverse (Matrix.toEuclideanCLM (n:=D) (𝕜:=ℂ) A) b)))‖≤ε/2 ∧
      (physicalLower I 72000).conditionalOutput UA Ub
        (Repetition.basis (PhysicalExecution.initialIndex a n (preparationExponent κ)))=
          pureDensity (WithLp.ofLp x) := by
  simpa only [successProbability_refines,conditionalOutput_refines] using
    PhysicalExecution.execution_correct I h' f A hA hunit hinv hε0 hε1 UA henc Ub b hb hcol ht

/-- A single constructed primitive tree simultaneously has the exact execution
semantics, literal local gates/ports, attached elementary budget, exact query
counts and original workspace bound. No implementation certificate is assumed. -/
theorem physical_execution_complete (I : PhysicalProgram.Implementation a n (ε:=ε) h) :
    PhysicalSafety I (physicalSyntax I 72000) ∧
    (∀ (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
      (select : Bool → Bool) (v : Fin (Fintype.card (PhysicalProgram.Register a n (preparationExponent κ))) → ℂ),
      (physicalLower I 72000).executeDensity UA Ub select v=
        (PhysicalExecution.execution I).executeDensity UA Ub select v) ∧
    (physicalSyntax I 72000).cost≤PhysicalExecution.elementaryBudget I ∧
    Repetition.matrixDepth (physicalLower I 72000)=72000*(PhysicalExecution.runCircuit I).matrixQueries ∧
    (physicalLower I 72000).vectorDepth=72000*(PhysicalExecution.runCircuit I).vectorQueries ∧
    Repetition.instrumentDepth (physicalLower I 72000)=(physicalSyntax I 72000).cost+1 ∧
    Repetition.RegisterBound (Fintype.card (PhysicalProgram.Register a n (preparationExponent κ)))
      (physicalLower I 72000) :=
  ⟨physicalSyntax_safe I 72000,execution_refines I,elementaryBudget_attached I,
    (physicalLower_query_depths I 72000).1,(physicalLower_query_depths I 72000).2,
    physicalLower_instrumentDepth I 72000,physicalLower_registerBound I 72000⟩

end OptimalQLS.Refinement.CostedExecution
