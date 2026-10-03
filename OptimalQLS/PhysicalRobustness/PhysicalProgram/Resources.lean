import OptimalQLS.PhysicalRobustness.PhysicalProgram.Correctness
import OptimalQLS.Refinement.PhysicalProgram.Uniform

/-! Physical width and original-scale bounds for the same emitted noisy list. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1000000
open scoped Classical Matrix.Norms.L2Operator
namespace OptimalQLS.PhysicalRobustness.PhysicalProgram
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform PhysicalPadding Refinement
open Refinement.PhysicalProgram
variable {a n : ℕ} {κ ŝ ε : ℝ}

theorem Implementation.vector_bound_uniform (I : Implementation a n κ ŝ ε)
    {t : ℝ} (h : BudgetParameters (2*κ) t (9*ŝ/8)) :
    ((I.circuit.toQuery (gateEval a n _ (CompilerAttachment.preparationExponent_pos I.budget))).vectorQueries : ℝ)<
      120000001*((2*κ)/t) := by
  rw [I.exact_counts.2.1]
  push_cast
  have hr : 1≤(2*κ)/t := (le_div_iff₀ h.scale_pos).mpr (by simpa using h.scale_le_kappa)
  linarith [h.reflectionBudget_scale_bound]

/-- Transfer to the original solution scale has a universal factor three, and
changes none of the lists, query ports, or register dimensions. -/
theorem Implementation.original_scale_bounds (I : Implementation a n κ ŝ ε)
    {s t : ℝ} (h : BudgetParameters (2*κ) t (9*ŝ/8))
    (hs : 0<s) (hst : 2*s/3≤t) :
    ((I.circuit.toQuery (gateEval a n _ (CompilerAttachment.preparationExponent_pos I.budget))).vectorQueries : ℝ)<
      360000003*(κ/s) ∧
    (I.circuit.workGates : ℝ)<400000000000000*κ*(a+1)+2100000000000*(κ/s)*(n+1)+
      150000027051856*κ*(a+1)*Real.log (1/(ε/4096)) := by
  have htransfer := noisy_vector_coefficient_transfer (κ := κ) (s := s) (t := t) (by linarith [I.kappa_ge_two]) hs hst
  constructor
  · exact (I.vector_bound_uniform h).trans_le (by nlinarith)
  · have hp := I.work_bound_uniform h
    have hm := mul_le_mul_of_nonneg_right htransfer (show (0:ℝ)≤700000000000*(n+1) by positivity)
    nlinarith

/-- The proof-only analysis scale is discharged from the original noisy input
promises, and the source cost is charged to its original solution norm. -/
theorem Implementation.input_resources (I : Implementation a n κ ŝ ε)
    {D : Type*} [Fintype D] [DecidableEq D] (f : D ↪ Bits n)
    (A : Matrix D D ℂ) (hA : A.IsHermitian) (hunit : IsUnit A) (hAnorm : ‖A‖≤1)
    (B : Matrix (Bits n) (Bits n) ℂ) (hB : B.IsHermitian) (hBn : ‖B‖≤1)
    (b : EuclideanSpace ℂ D) (hb : ‖b‖=1)
    {δ : ℝ} (hδ : 0≤δ) (hinv : ‖Ring.inverse A‖≤κ)
    (hpert : ‖B-zeroExtend f A‖≤δ) (hsmall : κ*δ≤1/4)
    (hestlo : solutionScale 1 A b/2≤ŝ) (hesthi : ŝ≤2*solutionScale 1 A b) :
    ((I.circuit.toQuery (gateEval a n _ (CompilerAttachment.preparationExponent_pos I.budget))).vectorQueries : ℝ)<
      360000003*(κ/solutionScale 1 A b) ∧
    (I.circuit.workGates : ℝ)<400000000000000*κ*(a+1)+2100000000000*(κ/solutionScale 1 A b)*(n+1)+
      150000027051856*κ*(a+1)*Real.log (1/(ε/4096)) := by
  have hg := noisy_graph_promises f A hA hunit hAnorm B hB hBn b hb
    I.kappa_ge_two hδ hinv hpert hsmall hestlo hesthi
  dsimp only at hg
  obtain ⟨h,_,_,_,_,_,hst⟩ := hg
  exact I.original_scale_bounds h (by linarith [I.estimate_lower]) hst

theorem Implementation.qubit_bound (I : Implementation a n κ ŝ ε) :
    Fintype.card (Register a n (preparationExponent (2*κ)))=2^(n+3*a+2*preparationExponent (2*κ)+27) ∧
    n+3*a+2*preparationExponent (2*κ)+27≤n+3*a+2*Nat.log2 ⌈2*κ⌉₊+83 :=
  run_qubit_bound a n I.budget

/-- Every work leaf is one of the placed physical at-most-two-qubit gates. -/
theorem Implementation.local_gates (I : Implementation a n κ ŝ ε) :
    ∀ g, NamedInstruction.gate g∈I.circuit → g.arity≤2 :=
  fun g _ => Gate.arity_le_two g

end OptimalQLS.PhysicalRobustness.PhysicalProgram
