import OptimalQLS.Refinement.PhysicalExecution

/-! # Explicit resources of the repeated actual elementary program -/
noncomputable section
namespace OptimalQLS.Refinement.PhysicalExecution
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform PhysicalPadding LowerBounds Repetition
open scoped Matrix.Norms.L2Operator
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 500000
variable {a n : ℕ} {κ s ŝ ε : ℝ} {h : BudgetParameters κ s ŝ}

/-- The physical unitary list is repeated at most72000 times; each measurement
and feedback list is the one proved in PhysicalMeasurement. -/
def elementaryBudget (I : PhysicalProgram.Implementation a n (ε := ε) h) : ℕ :=
  72000*I.circuit.workGates+
    72000*(Fintype.card (PhysicalMeasurement.AuxWire a (preparationExponent κ))+
      2*Fintype.card (PhysicalMeasurement.AuxWire a (preparationExponent κ) ⊕ Fin n))+
    2*Fintype.card (PhysicalMeasurement.AuxWire a (preparationExponent κ) ⊕ Fin n)

theorem elementaryBudget_le (I : PhysicalProgram.Implementation a n (ε := ε) h) :
    elementaryBudget I≤72000*I.circuit.workGates+220000*(n+3*a+2*preparationExponent κ+27) := by
  have hm := PhysicalMeasurement.repetition_measure_reset_bound a n (preparationExponent κ)
  unfold elementaryBudget
  omega

theorem width_linear (a n : ℕ) {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ) :
    ((n+3*a+2*preparationExponent κ+27 : ℕ) : ℝ)≤(n : ℝ)+47*κ*(a+1) := by
  have hw := (PhysicalProgram.run_qubit_bound a n h).2
  have hw' : ((n+3*a+2*preparationExponent κ+27 : ℕ) : ℝ)≤
      (n : ℝ)+3*a+2*(Nat.log2 ⌈κ⌉₊ : ℝ)+83 := by exact_mod_cast hw
  have hl : (Nat.log2 ⌈κ⌉₊ : ℝ)≤(⌈κ⌉₊ : ℝ) := by exact_mod_cast Nat.log2_le_self ⌈κ⌉₊
  have hc := Nat.ceil_lt_add_one h.kappa_pos.le
  have ha := Nat.cast_nonneg (α := ℝ) a
  have hka := mul_le_mul_of_nonneg_right h.kappa_ge_two ha
  nlinarith only [hw',hl,hc,ha,hka,h.kappa_ge_two]

theorem execution_matrix_bound (I : PhysicalProgram.Implementation a n (ε := ε) h)
    (hε0 : 0<ε) (hε1 : ε<1/2) :
    (Repetition.matrixDepth (execution I) : ℝ)<79200000000000*κ*Real.log (1/ε) := by
  have hc : ((runCircuit I).matrixQueries : ℝ)<2*mainBudget κ+840096*κ*Real.log (1/(ε/1024)) := by
    have he : (runCircuit I).matrixQueries=2*mainBudget κ+
        (I.filter.toQuery (GraphAttachedGate.eval a)).matrixQueries+
        (I.correction.toQuery (SingleFlagGate.eval a)).matrixQueries := I.exact_counts.1
    rw [he]
    push_cast
    nlinarith only [I.filter_matrix,I.correction_matrix]
  have hb := (repetition_query_bounds h hε0 hε1 (runCircuit I).matrixQueries
    (runCircuit I).vectorQueries hc I.exact_counts.2.1).1
  have hd : (Repetition.matrixDepth (execution I) : ℝ)≤((72000*(runCircuit I).matrixQueries : ℕ) : ℝ) :=
    by exact_mod_cast (execution_query_depths I).1
  exact hd.trans_lt hb

theorem execution_vector_bound (I : PhysicalProgram.Implementation a n (ε := ε) h)
    {t : ℝ} (h' : BudgetParameters κ t ŝ) :
    ((execution I).vectorDepth : ℝ)<8640000072000*(κ/t) := by
  have hc : (runCircuit I).vectorQueries=2*reflectionBudget κ ŝ+1 := I.exact_counts.2.1
  have hb := one_run_vector_bound h'
  rw [←hc] at hb
  have hs := mul_lt_mul_of_pos_left hb (by norm_num : (0 : ℝ)<72000)
  have hd : ((execution I).vectorDepth : ℝ)≤((72000*(runCircuit I).vectorQueries : ℕ) : ℝ) :=
    by exact_mod_cast (execution_query_depths I).2
  push_cast at hd
  nlinarith only [hs,hd]

/-- Both unitary leaves and the explicitly synthesized measurement/reset lists
fit the paper's two-term elementary-work bound for the actual hidden scale. -/
theorem elementaryBudget_bound (I : PhysicalProgram.Implementation a n (ε := ε) h)
    {t : ℝ} (h' : BudgetParameters κ t ŝ) (hε0 : 0<ε) (hε1 : ε<1/2) :
    (elementaryBudget I : ℝ)<40000000000000000000*κ*(a+1)*Real.log (1/ε)+
      60000000000000000*(κ/t)*(n+1) := by
  have hw := I.work_bound_uniform h'
  have he := log_refinement_accuracy hε0 hε1
  have hl := log_accuracy_lower hε0 hε1
  have hq := width_linear a n h'
  have hc : (elementaryBudget I : ℝ)≤72000*(I.circuit.workGates : ℝ)+
      220000*((n+3*a+2*preparationExponent κ+27 : ℕ) : ℝ) := by exact_mod_cast elementaryBudget_le I
  have ht : 0<t := by linarith [h'.scale_ge_one]
  have hs : 1≤κ/t := (le_div_iff₀ ht).mpr (by simpa using h'.scale_le_kappa)
  have hsn := mul_le_mul_of_nonneg_right hs (show 0≤(n : ℝ)+1 by positivity)
  have hk := h'.kappa_pos
  have hx : 0≤κ*((a : ℝ)+1) := by positivity
  have hxl := mul_le_mul_of_nonneg_left hl hx
  have hel := mul_le_mul_of_nonneg_left he (show 0≤3341621776*κ*((a : ℝ)+1) by positivity)
  have hwork := mul_lt_mul_of_pos_left hw (by norm_num : (0 : ℝ)<72000)
  have hwidth := mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ)≤220000)
  nlinarith only [hc,hwork,hwidth,hel,hxl,hsn,hx]

end OptimalQLS.Refinement.PhysicalExecution
