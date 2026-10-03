import OptimalQLS.Refinement.CostedExecution.Refinement
import OptimalQLS.Refinement.PhysicalResources

/-! The costed syntax is attached to the fixed physical QLSA implementation.
The named gates and query ports are copied, never replaced by arbitrary work. -/
noncomputable section
open scoped Classical
namespace OptimalQLS.Refinement.CostedExecution
open Matrix LowerBounds PolynomialTransform Repetition.Physical
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 16384
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

section Reindex
variable {G A B W : Type*} [Fintype W] [DecidableEq W] {w : ℕ}

def reindexNamedInstruction (E : W ≃ Fin w) : NamedInstruction G A B W → NamedInstruction G A B (Fin w)
  | .gate g => .gate g
  | .matrixCall p b => .matrixCall (Repetition.reindexPort E p) b
  | .vectorCall p b => .vectorCall (Repetition.reindexPort E p) b

def reindexNamed (E : W ≃ Fin w) (c : NamedCircuit G A B W) : NamedCircuit G A B (Fin w) :=
  c.map (reindexNamedInstruction E)

theorem reindexNamed_toQuery (E : W ≃ Fin w) (gate : G → Matrix.unitaryGroup W ℂ)
    (c : NamedCircuit G A B W) :
    (reindexNamed E c).toQuery (fun g=>rewireUnitary E (gate g)) =
      Repetition.reindexCircuit E (c.toQuery gate) := by
  simp only [reindexNamed,NamedCircuit.toQuery,Repetition.reindexCircuit,List.map_map]
  apply List.map_congr_left
  intro x _
  cases x <;> rfl

theorem reindexNamed_workGates (E : W ≃ Fin w) (c : NamedCircuit G A B W) :
    (reindexNamed E c).workGates = c.workGates := by
  induction c with
  | nil => rfl
  | cons g c ih => cases g <;> simp_all [reindexNamed,reindexNamedInstruction,NamedCircuit.workGates]
end Reindex

attribute [local irreducible] Repetition.repeatProgram repeated Program.lower

open Preparation PhysicalPadding TransducerCompiler BinaryClock
variable {a n : ℕ} {κ s ŝ ε : ℝ} {h : BudgetParameters κ s ŝ}

def physicalGate (I : PhysicalProgram.Implementation a n (ε:=ε) h) :
    PhysicalProgram.Gate a n (preparationExponent κ) →
      Matrix.unitaryGroup (Fin (Fintype.card (PhysicalProgram.Register a n (preparationExponent κ)))) ℂ :=
  fun g : PhysicalProgram.Gate a n (preparationExponent κ)=>
    rewireUnitary (Fintype.equivFin (PhysicalProgram.Register a n (preparationExponent κ)))
      (PhysicalProgram.gateEval a n (preparationExponent κ) (CompilerAttachment.preparationExponent_pos h) g)

def physicalSyntax (I : PhysicalProgram.Implementation a n (ε:=ε) h) (R : ℕ) :
    Program (PhysicalProgram.Gate a n (preparationExponent κ)) (Bits a × Bits n) (Bits n)
      (PhysicalMeasurement.AuxWire a (preparationExponent κ)) (Fin n)
      (Fintype.card (PhysicalProgram.Register a n (preparationExponent κ))) :=
  repeated (HadamardClock.bitsFinEquiv n)
    (reindexNamed (Fintype.equivFin (PhysicalProgram.Register a n (preparationExponent κ))) I.circuit)
    (PhysicalMeasurement.acceptancePattern a (preparationExponent κ))
    ((PhysicalMeasurement.registerCoordinates a n (preparationExponent κ)).symm
      (PhysicalProgram.initial a n (preparationExponent κ))) (0 : Fin (2^n)) R

def physicalLower (I : PhysicalProgram.Implementation a n (ε:=ε) h) (R : ℕ) :
    FiniteOracleProgram (Bits a × Bits n) (Bits n) (2^n)
      (Fintype.card (PhysicalProgram.Register a n (preparationExponent κ))) :=
  (physicalSyntax I R).lower (PhysicalMeasurement.finiteRegisterCoordinates a n (preparationExponent κ))
    (HadamardClock.bitsFinEquiv n) (physicalGate I)

/-- The fully lowered primitive execution has the same success AND failure
densities as the existing execution, on every input and every oracle pair. -/
theorem physicalLower_refines (I : PhysicalProgram.Implementation a n (ε:=ε) h)
    (R : ℕ) (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (select : Bool → Bool) (v : Fin (Fintype.card (PhysicalProgram.Register a n (preparationExponent κ))) → ℂ) :
    (physicalLower I R).executeDensity UA Ub select v =
      (Repetition.repeatProgram (finiteRun (PhysicalExecution.runCircuit I))
        (finiteAccept (PhysicalExecution.dataEmbedding a n (preparationExponent κ)))
        (PhysicalExecution.initialIndex a n (preparationExponent κ)) (0 : Fin (2^n)) R).executeDensity UA Ub select v := by
  have hh := repeated_refines
    (PhysicalMeasurement.finiteRegisterCoordinates a n (preparationExponent κ))
    (HadamardClock.bitsFinEquiv n) (physicalGate I) UA Ub select
    (reindexNamed (Fintype.equivFin (PhysicalProgram.Register a n (preparationExponent κ))) I.circuit)
    (PhysicalMeasurement.acceptancePattern a (preparationExponent κ))
    ((PhysicalMeasurement.registerCoordinates a n (preparationExponent κ)).symm
      (PhysicalProgram.initial a n (preparationExponent κ))) (0 : Fin (2^n)) R v
  have hc : (reindexNamed (Fintype.equivFin (PhysicalProgram.Register a n (preparationExponent κ))) I.circuit).toQuery (physicalGate I)=
      finiteRun (PhysicalExecution.runCircuit I) := reindexNamed_toQuery
        (Fintype.equivFin (PhysicalProgram.Register a n (preparationExponent κ)))
        (PhysicalProgram.gateEval a n _ (CompilerAttachment.preparationExponent_pos h)) I.circuit
  rw [hc] at hh
  simpa only [den,physicalLower,physicalSyntax,physicalGate,finiteRun,PhysicalExecution.runCircuit,
    PhysicalExecution.acceptanceEmbedding_exact,PhysicalMeasurement.acceptanceEmbedding,
    PhysicalMeasurement.finiteRegisterCoordinates,Equiv.trans_apply,Equiv.apply_symm_apply,
    PhysicalExecution.initialIndex] using hh

theorem execution_refines (I : PhysicalProgram.Implementation a n (ε:=ε) h)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (select : Bool → Bool) (v : Fin (Fintype.card (PhysicalProgram.Register a n (preparationExponent κ))) → ℂ) :
    (physicalLower I 72000).executeDensity UA Ub select v =
      (PhysicalExecution.execution I).executeDensity UA Ub select v :=
  physicalLower_refines I 72000 UA Ub select v

/-- Structural primitive-node cost on the same emitted execution. -/
theorem physicalSyntax_cost (I : PhysicalProgram.Implementation a n (ε:=ε) h) (R : ℕ) :
    (physicalSyntax I R).cost ≤
      R*(I.circuit.workGates+Fintype.card (PhysicalMeasurement.AuxWire a (preparationExponent κ))+
        2*Fintype.card (PhysicalMeasurement.AuxWire a (preparationExponent κ) ⊕ Fin n))+
        2*Fintype.card (PhysicalMeasurement.AuxWire a (preparationExponent κ) ⊕ Fin n) := by
  unfold physicalSyntax
  simpa only [reindexNamed_workGates] using repeat_cost
    (HadamardClock.bitsFinEquiv n)
    (reindexNamed (Fintype.equivFin (PhysicalProgram.Register a n (preparationExponent κ))) I.circuit)
    (PhysicalMeasurement.acceptancePattern a (preparationExponent κ))
    ((PhysicalMeasurement.registerCoordinates a n (preparationExponent κ)).symm
      (PhysicalProgram.initial a n (preparationExponent κ))) (0 : Fin (2^n)) R

/-- This is the previously missing attachment: elementaryBudget bounds the
cost of the primitive syntax whose lowering refines execution I. -/
theorem elementaryBudget_attached (I : PhysicalProgram.Implementation a n (ε:=ε) h) :
    (physicalSyntax I 72000).cost ≤ PhysicalExecution.elementaryBudget I := by
  have hh := physicalSyntax_cost I 72000
  simpa only [PhysicalExecution.elementaryBudget,Nat.mul_add,Nat.add_assoc] using hh

theorem physical_cost_bound (I : PhysicalProgram.Implementation a n (ε:=ε) h)
    {t : ℝ} (h' : BudgetParameters κ t ŝ) (hε0 : 0<ε) (hε1 : ε<1/2) :
    ((physicalSyntax I 72000).cost : ℝ)<
      40000000000000000000*κ*(a+1)*Real.log (1/ε)+60000000000000000*(κ/t)*(n+1) := by
  have hc : ((physicalSyntax I 72000).cost : ℝ)≤(PhysicalExecution.elementaryBudget I : ℝ) := by
    exact_mod_cast elementaryBudget_attached I
  exact hc.trans_lt (PhysicalExecution.elementaryBudget_bound I h' hε0 hε1)

end OptimalQLS.Refinement.CostedExecution
