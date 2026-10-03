import OptimalQLS.Reduction.DirectResources

/-! # Original-input correctness of the actual primitive instruction tree -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open scoped Classical Matrix.Norms.L2Operator
namespace OptimalQLS.Reduction.DirectCosted
open Matrix TransducerCompiler BinaryClock PolynomialTransform PhysicalPadding
open Refinement Refinement.PhysicalExecution Refinement.Repetition LowerBounds CostedExecution
variable {a n : ℕ} {κ s ŝ ε : ℝ} {h : BudgetParameters κ s ŝ}
attribute [local irreducible] CostedExecution.repeated CostedExecution.Program.lower Repetition.repeatProgram

theorem algorithm_correct (I : PhysicalProgram.Implementation a (n+1) (ε := ε) h)
    {D : Type*} [Fintype D] [DecidableEq D] [Nonempty D] (f : D ↪ Bits n)
    {α : ℝ} (A : Matrix D D ℂ) (hA : IsUnit A) (b : EuclideanSpace ℂ D) (hb : ‖b‖=1)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (henc : IsBlockEncoding (fun _ : Fin a=>false) α 0 UA (zeroExtend f A))
    (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (hcol : ∀ i,Ub i (fun _ : Fin n=>false)=coordinateIsometry f b i)
    (hi : α*‖Ring.inverse A‖≤κ)
    (hlo : 3*solutionScale α A b/8≤ŝ) (hhi : ŝ≤5*solutionScale α A b/2)
    (hε0 : 0<ε) (hε1 : ε<1/2) :
    (2 : ℝ)/3<(algorithm I).successProbability UA Ub
      (basis (AdaptedExecution.initialIndex a n (preparationExponent κ))) ∧
    ∃ x : EuclideanSpace ℂ (Fin (2^n)), ‖x‖=1 ∧
      ‖x-outputCoordinates n (coordinateIsometry f
        (NormedSpace.normalize (WithLp.toLp 2 (A⁻¹*ᵥWithLp.ofLp b))))‖≤ε ∧
      (algorithm I).conditionalOutput UA Ub
        (basis (AdaptedExecution.initialIndex a n (preparationExponent κ)))=
        pureDensity (WithLp.ofLp x) := by
  have hc := DirectExecution.accepted_correct I f A hA b hb UA henc Ub hcol hi hlo hhi hε0 hε1
  have he := DirectExecution.execution_success I UA Ub hc.2.2.2
  have heq : compressed (PhysicalAdapter.adapted I)
      (Preparation.CompilerAttachment.preparationExponent_pos h) 600000=DirectExecution.execution I := rfl
  refine ⟨?_,NormedSpace.normalize (DirectExecution.accepted I UA Ub),hc.2.1,hc.2.2.1,?_⟩
  · rw [algorithm,success_eq,heq]
    exact he.1
  · rw [algorithm,output_eq,heq]
    exact he.2

/-- The exact same code receives the sharper vector/work bounds for the
actual hidden scale, which is derived only after the public code is chosen. -/
theorem algorithm_input_resources (I : PhysicalProgram.Implementation a (n+1) (ε := ε) h)
    {D : Type*} [Fintype D] [DecidableEq D] [Nonempty D] (f : D ↪ Bits n)
    {α : ℝ} (A : Matrix D D ℂ) (hA : IsUnit A) (b : EuclideanSpace ℂ D) (hb : ‖b‖=1)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (henc : IsBlockEncoding (fun _ : Fin a=>false) α 0 UA (zeroExtend f A))
    (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (hcol : ∀ i,Ub i (fun _ : Fin n=>false)=coordinateIsometry f b i)
    (hi : α*‖Ring.inverse A‖≤κ)
    (hlo : 3*solutionScale α A b/8≤ŝ) (hhi : ŝ≤5*solutionScale α A b/2)
    (hε0 : 0<ε) (hε1 : ε<1/2) :
    ((algorithm I).vectorDepth : ℝ)<72000000600000*(κ/solutionScale α A b) ∧
    ((algorithmSyntax I).cost : ℝ)<300000000000000000000*κ*(a+1)*Real.log (1/ε)+
      1000000000000000000*(κ/solutionScale α A b)*(n+1) := by
  have hp := (active_input_normalization f A hA b hb UA henc Ub hcol h.kappa_ge_two hi hlo hhi).2.2.2.2.2.2.1
  exact ⟨vector_bound I hp,work_bound I hp hε0 hε1⟩

end OptimalQLS.Reduction.DirectCosted
