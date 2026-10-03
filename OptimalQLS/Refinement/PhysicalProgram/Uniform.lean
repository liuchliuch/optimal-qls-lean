import OptimalQLS.Refinement.PhysicalProgram.Complete

/-! # Closed uniform physical-run endpoint and ordinary active-bit specialization -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open scoped Classical Matrix.Norms.L2Operator
namespace OptimalQLS.Refinement.PhysicalProgram
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform PhysicalPadding

/-- This universal predicate follows from one selected triple of physical lists;
it is not an input certificate to any synthesis result. -/
def UniformCorrect {a n : ℕ} {κ s ŝ ε : ℝ} {h : BudgetParameters κ s ŝ}
    (I : Implementation a n (ε := ε) h) : Prop :=
  ∀ (D : Type) [Fintype D] [DecidableEq D] (f : D ↪ Bits n)
    (A : Matrix D D ℂ), A.IsHermitian → IsUnit A → ‖Ring.inverse A‖≤κ →
    ∀ (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ),
    IsBlockEncoding (fun _ : Fin a=>false) 1 0 UA (zeroExtend f A) →
    ∀ (Ub : Matrix.unitaryGroup (Bits n) ℂ) (b : EuclideanSpace ℂ D), ‖b‖=1 →
    (∀ i,Ub i (fun _ : Fin n=>false)=coordinateIsometry f b i) → s=solutionScale 1 A b →
    I.accepted UA Ub≠0 ∧
      ‖NormedSpace.normalize (I.accepted UA Ub)-coordinateIsometry f
        (NormedSpace.normalize (Ring.inverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) b))‖≤ε/2 ∧
      1/65536<‖I.accepted UA Ub‖^2

/-- A finite physical list is chosen before the embedding, matrix, full supplied
oracles, and source vector. Its success probability is also at most one. -/
theorem physical_run_uniform (a n : ℕ) {κ s ŝ ε : ℝ} (h : BudgetParameters κ s ŝ)
    (hε0 : 0<ε) (hε1 : ε<1/2) :
    ∃ I : Implementation a n (ε := ε) h,
      SingleControlled I.circuit ∧ UniformCorrect I ∧
      ∀ UA Ub, ‖I.accepted UA Ub‖^2≤1 := by
  obtain ⟨I⟩ := implementation_exists a n h hε0 hε1
  refine ⟨I,I.singleControlled,?_,I.probability_le_one⟩
  intro D _ _ f A hA hu hi UA henc Ub b hb hcol hs
  exact I.correctness f A hA hu hi hε0 hε1 UA henc Ub b hb hcol hs

/-- Canonical non-power-of-two logical dimensions are embedded by their actual
low-first data bits; the supplied oracle is neither replaced nor permuted. -/
theorem Implementation.activeDataBits_correctness {d a : ℕ} [NeZero d]
    {κ s ŝ ε : ℝ} {h : BudgetParameters κ s ŝ}
    (I : Implementation a (dataQubits d) (ε := ε) h)
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (hunit : IsUnit A)
    (hinv : ‖Ring.inverse A‖≤κ) (hε0 : 0<ε) (hε1 : ε<1/2)
    (UA : Matrix.unitaryGroup (Bits a × Bits (dataQubits d)) ℂ)
    (henc : IsBlockEncoding (fun _ : Fin a=>false) 1 0 UA (zeroExtend (activeDataBits d) A))
    (Ub : Matrix.unitaryGroup (Bits (dataQubits d)) ℂ) (b : DataSpace d) (hb : ‖b‖=1)
    (hcol : ∀ i,Ub i (fun _ : Fin (dataQubits d)=>false)=coordinateIsometry (activeDataBits d) b i)
    (hs : s=solutionScale 1 A b) :
    I.accepted UA Ub≠0 ∧
      ‖NormedSpace.normalize (I.accepted UA Ub)-coordinateIsometry (activeDataBits d)
        (NormedSpace.normalize (Ring.inverse (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A) b))‖≤ε/2 ∧
      1/65536<‖I.accepted UA Ub‖^2 :=
  I.correctness (activeDataBits d) A hA hunit hinv hε0 hε1 UA henc Ub b hb hcol hs

theorem run_qubit_bound (a n : ℕ) {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ) :
    Fintype.card (Register a n (preparationExponent κ))=2^(n+3*a+2*preparationExponent κ+27) ∧
    n+3*a+2*preparationExponent κ+27≤n+3*a+2*Nat.log2 ⌈κ⌉₊+83 := by
  refine ⟨register_card a n _,?_⟩
  have he := appendixA2_qubits h
  simp only [auxiliaryQubits] at he
  omega

end OptimalQLS.Refinement.PhysicalProgram
