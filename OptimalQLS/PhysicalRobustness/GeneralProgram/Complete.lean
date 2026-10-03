import OptimalQLS.PhysicalRobustness.GeneralProgram.Safety

/-! Closed general-input noisy solver: the actual word precedes every hidden input. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1000000
open scoped Classical Matrix.Norms.L2Operator
namespace OptimalQLS.PhysicalRobustness.GeneralProgram
open Matrix LowerBounds PhysicalPadding Reduction TransducerCompiler BinaryClock PolynomialTransform
open Refinement Refinement.PhysicalExecution Refinement.Repetition

/-- No solver certificate or realization premise is supplied by the input. -/
def UniformGuarantee {a n : ℕ} {κ ŝ ε : ℝ} (I : Implementation a n κ ŝ ε) : Prop :=
  ∀ (D : Type) [Fintype D] [DecidableEq D] (f : D ↪ Bits n)
    (α δ : ℝ) (A : Matrix D D ℂ), IsUnit A → ‖A‖≤α →
    ∀ (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ),
    IsBlockEncoding (fun _ : Fin a=>false) α δ UA (zeroExtend f A) →
    ∀ (Ub : Matrix.unitaryGroup (Bits n) ℂ) (b : EuclideanSpace ℂ D), ‖b‖=1 →
    (∀ i,Ub i (fun _ : Fin n=>false)=coordinateIsometry f b i) →
    α*‖Ring.inverse A‖≤κ → κ*δ/α≤1/4 →
    solutionScale α A b/2≤ŝ → ŝ≤2*solutionScale α A b →
    ((physicalExecution I).vectorDepth : ℝ)<216000001800000*(κ/solutionScale α A b) ∧
    ((physicalSyntax I).cost : ℝ)<3000000000000000000000*κ*(a+1)*Real.log (1/ε)+
      3000000000000000000*(κ/solutionScale α A b)*(n+1) ∧
    (2 : ℝ)/3<(physicalExecution I).successProbability UA Ub
      (basis (AdaptedExecution.initialIndex a n (preparationExponent (2*κ)))) ∧
    ∃ x : EuclideanSpace ℂ (Fin (2^n)), ‖x‖=1 ∧
      ‖x-solution f A b‖≤ε+2*κ*δ/α ∧
      (physicalExecution I).conditionalOutput UA Ub
        (basis (AdaptedExecution.initialIndex a n (preparationExponent (2*κ))))=
        pureDensity (WithLp.ofLp x)

/-- A single selected list and its actual physical measurement/reset execution
solve all approximate non-Hermitian inputs at every active embedding. -/
theorem general_noisy_physical_algorithm (a n : ℕ) {κ ŝ ε : ℝ}
    (hκ : 2≤κ) (hlo : 1/2≤ŝ) (hhi : ŝ≤2*κ) (hε : 0<ε) (hε1 : ε<1/2) :
    ∃ I : Implementation a n κ ŝ ε,
      PhysicallySafe I ∧ PhysicalAdapter.Safe (circuit I) ∧
      (matrixDepth (physicalExecution I) : ℝ)<534000000000000000*κ*Real.log (1/ε) ∧
      RegisterBound (2^(n+3*a+2*preparationExponent (2*κ)+31)) (physicalExecution I) ∧
      n+3*a+2*preparationExponent (2*κ)+31≤n+3*a+2*Nat.log2 ⌈2*κ⌉₊+87 ∧
      UniformGuarantee I := by
  obtain ⟨I⟩ := PhysicalRobustness.PhysicalProgram.implementation_exists a (n+1) hκ hlo hhi hε hε1
  refine ⟨I,physical_safe I,circuit_safe I,physicalExecution_matrix_bound I hε hε1,
    (physicalExecution_width_bound I).1,(physicalExecution_width_bound I).2,?_⟩
  intro D _ _ f α δ A hu hn UA henc Ub b hb hcol hi hs hlo hhi
  have hr := physicalExecution_input_resources I f A hu hn UA henc Ub b hb hcol hi hs hlo hhi hε hε1
  have hc := physicalExecution_correct I f A hu hn UA henc Ub b hb hcol hi hs hlo hhi hε hε1
  exact ⟨hr.1,hr.2,hc⟩

end OptimalQLS.PhysicalRobustness.GeneralProgram
