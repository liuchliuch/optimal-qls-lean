import OptimalQLS.Refinement.CostedExecution.Attachment
import OptimalQLS.Refinement.CostedExecution.Resources

/-! Exact resource extraction from the same typed physical syntax and its
normalized lowering, including terminal failure cleanup. -/
noncomputable section
open scoped Classical
namespace OptimalQLS.Refinement.CostedExecution
open Matrix LowerBounds PolynomialTransform Repetition.Physical
open Preparation PhysicalPadding TransducerCompiler BinaryClock
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 16384
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
attribute [local irreducible] repeated Program.lower
variable {a n : ℕ} {κ s ŝ ε : ℝ} {h : BudgetParameters κ s ŝ}

/-- Counts are read from the actual tree, and include all rejection branches,
even branches that have zero Born weight for a particular supplied oracle. -/
theorem physicalSyntax_calls (I : PhysicalProgram.Implementation a n (ε:=ε) h) (R : ℕ) :
    (physicalSyntax I R).matrixCalls=R*(PhysicalExecution.runCircuit I).matrixQueries ∧
    (physicalSyntax I R).vectorCalls=R*(PhysicalExecution.runCircuit I).vectorQueries := by
  letI : Nonempty (PhysicalMeasurement.AuxWire a (preparationExponent κ)) :=
    ⟨Sum.inl (Sum.inl ())⟩
  have hh := repeated_calls (HadamardClock.bitsFinEquiv n)
    (reindexNamed (Fintype.equivFin (PhysicalProgram.Register a n (preparationExponent κ))) I.circuit)
    (physicalGate I) (PhysicalMeasurement.acceptancePattern a (preparationExponent κ))
    ((PhysicalMeasurement.registerCoordinates a n (preparationExponent κ)).symm
      (PhysicalProgram.initial a n (preparationExponent κ))) (0 : Fin (2^n)) R
  have hc : (reindexNamed (Fintype.equivFin (PhysicalProgram.Register a n (preparationExponent κ)))
      I.circuit).toQuery (physicalGate I)=finiteRun (PhysicalExecution.runCircuit I) :=
    reindexNamed_toQuery (Fintype.equivFin (PhysicalProgram.Register a n (preparationExponent κ)))
      (PhysicalProgram.gateEval a n _ (CompilerAttachment.preparationExponent_pos h)) I.circuit
  rw [hc] at hh
  simpa only [physicalSyntax,finiteRun,
    Repetition.reindexCircuit_matrixQueries,Repetition.reindexCircuit_vectorQueries,
    PhysicalExecution.runCircuit] using hh

/-- Lowering does not change either worst-case oracle count. -/
theorem physicalLower_query_depths (I : PhysicalProgram.Implementation a n (ε:=ε) h) (R : ℕ) :
    Repetition.matrixDepth (physicalLower I R)=R*(PhysicalExecution.runCircuit I).matrixQueries ∧
    (physicalLower I R).vectorDepth=R*(PhysicalExecution.runCircuit I).vectorQueries := by
  constructor
  · exact (Program.lower_matrixCalls
      (PhysicalMeasurement.finiteRegisterCoordinates a n (preparationExponent κ))
      (HadamardClock.bitsFinEquiv n) (physicalGate I) (physicalSyntax I R)).trans
        (physicalSyntax_calls I R).1
  · exact (Program.lower_vectorCalls
      (PhysicalMeasurement.finiteRegisterCoordinates a n (preparationExponent κ))
      (HadamardClock.bitsFinEquiv n) (physicalGate I) (physicalSyntax I R)).trans
        (physicalSyntax_calls I R).2

/-- The query bounds also hold on every actual terminal path extracted by the
lowered execution semantics, without a nonzero-probability restriction. -/
theorem physicalLower_terminal_queries_le (I : PhysicalProgram.Implementation a n (ε:=ε) h)
    (R : ℕ) (psi : Fin (Fintype.card (PhysicalProgram.Register a n (preparationExponent κ))) → ℂ)
    (k : (physicalLower I R).Terminal) :
    ((physicalLower I R).terminalPath (.initial psi) k).matrixQueries≤
        R*(PhysicalExecution.runCircuit I).matrixQueries ∧
    ((physicalLower I R).terminalPath (.initial psi) k).vectorQueries≤
        R*(PhysicalExecution.runCircuit I).vectorQueries := by
  constructor
  · simpa only [VariableQueryPath.matrixQueries,zero_add,(physicalLower_query_depths I R).1]
      using Repetition.terminalPath_matrixQueries_le (physicalLower I R) (.initial psi) k
  · simpa only [VariableQueryPath.vectorQueries,zero_add,(physicalLower_query_depths I R).2]
      using Repetition.terminalPath_vectorQueries_le (physicalLower I R) (.initial psi) k

theorem physicalLower_instrumentDepth (I : PhysicalProgram.Implementation a n (ε:=ε) h) (R : ℕ) :
    Repetition.instrumentDepth (physicalLower I R)=(physicalSyntax I R).cost+1 :=
  Program.lower_instrumentDepth
    (PhysicalMeasurement.finiteRegisterCoordinates a n (preparationExponent κ))
    (HadamardClock.bitsFinEquiv n) (physicalGate I) (physicalSyntax I R)

/-- The complete lowered tree, including every measurement/reset branch and
final failure, stays in the original quantum register or the output register. -/
theorem physicalLower_registerBound (I : PhysicalProgram.Implementation a n (ε:=ε) h) (R : ℕ) :
    Repetition.RegisterBound
      (Fintype.card (PhysicalProgram.Register a n (preparationExponent κ))) (physicalLower I R) :=
  Program.lower_registerBound
    (PhysicalMeasurement.finiteRegisterCoordinates a n (preparationExponent κ))
    (HadamardClock.bitsFinEquiv n) (physicalGate I) (physicalSyntax I R)

theorem physicalLower_qubit_bound (I : PhysicalProgram.Implementation a n (ε:=ε) h) (R : ℕ) :
    Repetition.RegisterBound (2^(n+3*a+2*preparationExponent κ+27)) (physicalLower I R) ∧
    n+3*a+2*preparationExponent κ+27≤n+3*a+2*Nat.log2 ⌈κ⌉₊+83 := by
  obtain ⟨hc,hq⟩ := PhysicalProgram.run_qubit_bound a n h
  exact ⟨(congrArg (fun M=>Repetition.RegisterBound M (physicalLower I R)) hc).mp
    (physicalLower_registerBound I R),hq⟩

/-- Every terminal is charged by the named/measurement/X nodes on its actual
primitive branch. The theorem quantifies over failure and zero-weight leaves. -/
theorem physicalLower_terminalCost_le (I : PhysicalProgram.Implementation a n (ε:=ε) h)
    (k : (physicalLower I 72000).Terminal) :
    (physicalSyntax I 72000).terminalCost
      ((physicalSyntax I 72000).projectTerminal
        (PhysicalMeasurement.finiteRegisterCoordinates a n (preparationExponent κ))
        (HadamardClock.bitsFinEquiv n) (physicalGate I) k)≤PhysicalExecution.elementaryBudget I :=
  (Program.lowered_terminalCost_le
    (PhysicalMeasurement.finiteRegisterCoordinates a n (preparationExponent κ))
    (HadamardClock.bitsFinEquiv n) (physicalGate I) (physicalSyntax I 72000) k).trans
      (elementaryBudget_attached I)

theorem physicalLower_matrix_bound (I : PhysicalProgram.Implementation a n (ε:=ε) h)
    (hε0 : 0<ε) (hε1 : ε<1/2) :
    (Repetition.matrixDepth (physicalLower I 72000) : ℝ)<79200000000000*κ*Real.log (1/ε) := by
  have hc : ((PhysicalExecution.runCircuit I).matrixQueries : ℝ)<
      2*mainBudget κ+840096*κ*Real.log (1/(ε/1024)) := by
    have he : (PhysicalExecution.runCircuit I).matrixQueries=2*mainBudget κ+
        (I.filter.toQuery (GraphAttachedGate.eval a)).matrixQueries+
        (I.correction.toQuery (SingleFlagGate.eval a)).matrixQueries := I.exact_counts.1
    rw [he]
    push_cast
    nlinarith only [I.filter_matrix,I.correction_matrix]
  rw [(physicalLower_query_depths I 72000).1]
  exact (repetition_query_bounds h hε0 hε1 (PhysicalExecution.runCircuit I).matrixQueries
    (PhysicalExecution.runCircuit I).vectorQueries hc I.exact_counts.2.1).1

theorem physicalLower_vector_bound (I : PhysicalProgram.Implementation a n (ε:=ε) h)
    {t : ℝ} (h' : BudgetParameters κ t ŝ) :
    ((physicalLower I 72000).vectorDepth : ℝ)<8640000072000*(κ/t) := by
  have hc : (PhysicalExecution.runCircuit I).vectorQueries=2*reflectionBudget κ ŝ+1 := I.exact_counts.2.1
  have hb := one_run_vector_bound h'
  rw [←hc] at hb
  rw [(physicalLower_query_depths I 72000).2]
  push_cast
  have hh := mul_lt_mul_of_pos_left hb (by norm_num : (0 : ℝ)<72000)
  nlinarith only [hh]

theorem physicalLower_terminalCost_bound (I : PhysicalProgram.Implementation a n (ε:=ε) h)
    {t : ℝ} (h' : BudgetParameters κ t ŝ) (hε0 : 0<ε) (hε1 : ε<1/2)
    (k : (physicalLower I 72000).Terminal) :
    ((physicalSyntax I 72000).terminalCost
      ((physicalSyntax I 72000).projectTerminal
        (PhysicalMeasurement.finiteRegisterCoordinates a n (preparationExponent κ))
        (HadamardClock.bitsFinEquiv n) (physicalGate I) k) : ℝ)<
      40000000000000000000*κ*(a+1)*Real.log (1/ε)+60000000000000000*(κ/t)*(n+1) := by
  have hc : ((physicalSyntax I 72000).terminalCost
      ((physicalSyntax I 72000).projectTerminal
        (PhysicalMeasurement.finiteRegisterCoordinates a n (preparationExponent κ))
        (HadamardClock.bitsFinEquiv n) (physicalGate I) k) : ℝ)≤
      (PhysicalExecution.elementaryBudget I : ℝ) := by
    exact_mod_cast physicalLower_terminalCost_le I k
  exact hc.trans_lt (PhysicalExecution.elementaryBudget_bound I h' hε0 hε1)

end OptimalQLS.Refinement.CostedExecution
