import OptimalQLS.Reduction.DirectCostedResources

/-! # Actual query, gate and space bounds after physical input reduction -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open scoped Classical Matrix.Norms.L2Operator
namespace OptimalQLS.Reduction.DirectCosted
open Matrix TransducerCompiler BinaryClock PolynomialTransform PhysicalPadding
open Refinement Refinement.PhysicalExecution Refinement.Repetition LowerBounds CostedExecution
variable {a n : ℕ} {κ s ŝ ε : ℝ} {h : BudgetParameters κ s ŝ}
attribute [local irreducible] CostedExecution.repeated CostedExecution.Program.lower Repetition.repeatProgram

def algorithm (I : PhysicalProgram.Implementation a (n+1) (ε := ε) h) :=
  lower (PhysicalAdapter.adapted I) (Preparation.CompilerAttachment.preparationExponent_pos h) 600000

def algorithmSyntax (I : PhysicalProgram.Implementation a (n+1) (ε := ε) h) :=
  physicalSyntax (PhysicalAdapter.adapted I) 600000

theorem normalized_queries (I : PhysicalProgram.Implementation a (n+1) (ε := ε) h)
    (hε0 : 0<ε) (hε1 : ε<1/2) :
    ((runCircuit I).matrixQueries : ℝ)<1100000000*κ*Real.log (1/ε) := by
  have hc : ((runCircuit I).matrixQueries : ℝ)<
      2*mainBudget κ+840096*κ*Real.log (1/(ε/1024)) := by
    have he : (runCircuit I).matrixQueries=2*mainBudget κ+
        (I.filter.toQuery (GraphAttachedGate.eval a)).matrixQueries+
        (I.correction.toQuery (SingleFlagGate.eval a)).matrixQueries := I.exact_counts.1
    rw [he]
    push_cast
    nlinarith only [I.filter_matrix,I.correction_matrix]
  exact hc.trans (one_run_matrix_bound h hε0 hε1)

theorem matrix_bound (I : PhysicalProgram.Implementation a (n+1) (ε := ε) h)
    (hε0 : 0<ε) (hε1 : ε<1/2) :
    (matrixDepth (algorithm I) : ℝ)<1320000000000000*κ*Real.log (1/ε) := by
  have hq := normalized_queries I hε0 hε1
  have hc := (PhysicalAdapter.adapted_counts I).1
  rw [algorithm,(query_depths _ _ _).1,hc]
  change ((600000*(2*(runCircuit I).matrixQueries) : ℕ) : ℝ)<_
  push_cast
  nlinarith only [hq]

theorem vector_bound (I : PhysicalProgram.Implementation a (n+1) (ε := ε) h)
    {t : ℝ} (h' : BudgetParameters κ t ŝ) :
    ((algorithm I).vectorDepth : ℝ)<72000000600000*(κ/t) := by
  have hc := (PhysicalAdapter.adapted_counts I).2.1
  have hv : (runCircuit I).vectorQueries=2*reflectionBudget κ ŝ+1 := I.exact_counts.2.1
  have hb := one_run_vector_bound h'
  rw [←hv] at hb
  rw [algorithm,(query_depths _ _ _).2,hc]
  change ((600000*(runCircuit I).vectorQueries : ℕ) : ℝ)<_
  push_cast
  nlinarith only [hb]

theorem width_bound (I : PhysicalProgram.Implementation a (n+1) (ε := ε) h) :
    RegisterBound (2^(n+3*a+2*preparationExponent κ+31)) (algorithm I) ∧
      n+3*a+2*preparationExponent κ+31≤n+3*a+2*Nat.log2 ⌈κ⌉₊+87 := by
  refine ⟨register_bound _ _ _,?_⟩
  have hw := (PhysicalProgram.run_qubit_bound a (n+1) h).2
  omega

theorem work_bound (I : PhysicalProgram.Implementation a (n+1) (ε := ε) h)
    {t : ℝ} (h' : BudgetParameters κ t ŝ) (hε0 : 0<ε) (hε1 : ε<1/2) :
    ((algorithmSyntax I).cost : ℝ)<300000000000000000000*κ*(a+1)*Real.log (1/ε)+
      1000000000000000000*(κ/t)*(n+1) := by
  have hc0 := physicalSyntax_cost (PhysicalAdapter.adapted I) 600000
  have hg : ((PhysicalAdapter.adapted I).workGates : ℝ)≤
      (I.circuit.workGates : ℝ)+4801*(runCircuit I).matrixQueries := by
    exact_mod_cast (PhysicalAdapter.adapted_counts I).2.2
  have hc : ((algorithmSyntax I).cost : ℝ)≤600000*((PhysicalAdapter.adapted I).workGates : ℝ)+
      1800002*((n+3*a+2*preparationExponent κ+31 : ℕ) : ℝ) := by
    have hc' : (algorithmSyntax I).cost≤600000*(PhysicalAdapter.adapted I).workGates+
        1800002*(n+3*a+2*preparationExponent κ+31) := by
      change (physicalSyntax (PhysicalAdapter.adapted I) 600000).cost≤_
      omega
    exact_mod_cast hc'
  have hq := normalized_queries I hε0 hε1
  have hw := I.work_bound_uniform h'
  have hwidth := width_linear a (n+1) h'
  have hwidth' : ((n+3*a+2*preparationExponent κ+31 : ℕ) : ℝ)≤
      (n : ℝ)+4+47*κ*(a+1) := by
    push_cast at hwidth ⊢
    linarith only [hwidth]
  have hl := log_accuracy_lower hε0 hε1
  have he := log_refinement_accuracy hε0 hε1
  have hk := h'.kappa_pos
  have ha : (0 : ℝ)≤a := Nat.cast_nonneg a
  have hnn : (0 : ℝ)≤n := Nat.cast_nonneg n
  have hx : 0≤κ*((a : ℝ)+1) := by positivity
  have hxl := mul_le_mul_of_nonneg_left hl hx
  have hel := mul_le_mul_of_nonneg_left he (show 0≤3341621776*κ*((a : ℝ)+1) by positivity)
  have hqa := mul_le_mul_of_nonneg_left ha (show 0≤κ*Real.log (1/ε) by positivity)
  have ht : 0<t := by linarith only [h'.scale_ge_one]
  have hs : 1≤κ/t := (le_div_iff₀ ht).mpr (by simpa using h'.scale_le_kappa)
  have hsn := mul_le_mul_of_nonneg_right hs (show 0≤(n : ℝ)+1 by positivity)
  have hsp : 0≤κ/t := by positivity
  have hgw := mul_le_mul_of_nonneg_left hg (by norm_num : (0 : ℝ)≤600000)
  have hw' := mul_lt_mul_of_pos_left hw (by norm_num : (0 : ℝ)<600000)
  have hq' := mul_lt_mul_of_pos_left hq (by norm_num : (0 : ℝ)<2880600000)
  have hwidth'' := mul_le_mul_of_nonneg_left hwidth' (by norm_num : (0 : ℝ)≤1800002)
  push_cast at hw'
  nlinarith only [hc,hgw,hw',hq',hwidth'',hel,hxl,hqa,hsn,hsp,hnn,hx]

end OptimalQLS.Reduction.DirectCosted
