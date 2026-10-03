import OptimalQLS.PhysicalRobustness.PhysicalProgram.Resources

/-! Closed one-run noisy physical endpoint: one list before every hidden input. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1000000
open scoped Classical Matrix.Norms.L2Operator
namespace OptimalQLS.PhysicalRobustness.PhysicalProgram
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform PhysicalPadding Refinement
open Refinement.PhysicalProgram

/-- Universal input guarantee derived from synthesis, never an assumed realization. -/
def UniformCorrect {a n : ℕ} {κ ŝ ε : ℝ} (I : Implementation a n κ ŝ ε) : Prop :=
  ∀ (D : Type) [Fintype D] [DecidableEq D] (f : D ↪ Bits n)
    (A : Matrix D D ℂ), A.IsHermitian → IsUnit A → ‖A‖≤1 →
    ∀ (B : Matrix (Bits n) (Bits n) ℂ) (hB : B.IsHermitian)
      (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ),
    IsBlockEncoding (fun _ : Fin a=>false) 1 0 UA B →
    ∀ (Ub : Matrix.unitaryGroup (Bits n) ℂ) (b : EuclideanSpace ℂ D), ‖b‖=1 →
    (∀ i,Ub i (fun _ : Fin n=>false)=coordinateIsometry f b i) →
    ∀ (δ : ℝ), 0≤δ → ‖Ring.inverse A‖≤κ → ‖B-zeroExtend f A‖≤δ → κ*δ≤1/4 →
    solutionScale 1 A b/2≤ŝ → ŝ≤2*solutionScale 1 A b →
    I.accepted UA Ub≠0 ∧
      ‖NormedSpace.normalize (I.accepted UA Ub)-NormedSpace.normalize
        (highInverse (Matrix.toEuclideanCLM (n := Bits n) (𝕜 := ℂ) B)
          (matrixHermitian_symmetric B hB) δ (coordinateIsometry f b))‖≤ε/2 ∧
      1/262144<‖I.accepted UA Ub‖^2 ∧ ‖I.accepted UA Ub‖^2≤1

/-- A fixed finite, local, singly controlled actual program. The claim remains
explicitly about the normalized truncated target until the separate stability
and extraction theorems are applied. -/
theorem noisy_physical_run_complete (a n : ℕ) {κ ŝ ε : ℝ}
    (hκ : 2≤κ) (hlo : 1/2≤ŝ) (hhi : ŝ≤2*κ) (hε : 0<ε) (hε1 : ε<1/2) :
    ∃ I : Implementation a n κ ŝ ε,
      SingleControlled I.circuit ∧
      (∀ g,NamedInstruction.gate g∈I.circuit→g.arity≤2) ∧
      UniformCorrect I ∧
      (I.circuit.toQuery (gateEval a n _ (CompilerAttachment.preparationExponent_pos I.budget))).matrixQueries=
        2*mainBudget (2*κ)+(I.filter.toQuery (GraphAttachedGate.eval a)).matrixQueries+
          (I.correction.toQuery (SingleFlagGate.eval a)).matrixQueries ∧
      (I.circuit.toQuery (gateEval a n _ (CompilerAttachment.preparationExponent_pos I.budget))).vectorQueries=
        2*reflectionBudget (2*κ) (9*ŝ/8)+1 ∧
      I.circuit.workGates=I.preparation.workGates+I.filter.workGates+I.correction.workGates ∧
      Fintype.card (Register a n (preparationExponent (2*κ)))=2^(n+3*a+2*preparationExponent (2*κ)+27) := by
  obtain ⟨I⟩ := implementation_exists a n hκ hlo hhi hε hε1
  refine ⟨I,I.singleControlled,I.local_gates,?_,I.exact_counts.1,I.exact_counts.2.1,
    I.exact_counts.2.2,I.qubit_bound.1⟩
  intro D _ _ f A hA hu hAn B hB UA henc Ub b hb hcol δ hδ hinv hpert hsmall hlo hhi
  exact I.correctness f A hA hu hAn B hB UA henc Ub b hb hcol hδ hinv hpert hsmall hlo hhi hε hε1

end OptimalQLS.PhysicalRobustness.PhysicalProgram
