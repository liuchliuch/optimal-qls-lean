import OptimalQLS.Reduction.DirectCosted

/-! Exact structural resources of the same direct physical execution. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.Reduction.DirectCosted
open Matrix TransducerCompiler BinaryClock PolynomialTransform PhysicalPadding
open Refinement Refinement.Repetition LowerBounds CostedExecution
variable {a n ℓ : ℕ}
attribute [local irreducible] repeatProgram repeated CostedExecution.Program.lower

theorem physicalSyntax_cost (c : PhysicalAdapter.Circuit a n ℓ) (R : ℕ) :
    (physicalSyntax c R).cost≤R*(c.workGates+(3*a+2*ℓ+31)+2*(n+3*a+2*ℓ+31))+
      2*(n+3*a+2*ℓ+31) := by
  have hh := repeat_cost (HadamardClock.bitsFinEquiv n)
    (reindexNamed (Fintype.equivFin (PhysicalAdapter.Space a n ℓ)) c)
    (DirectMeasurement.acceptancePattern a ℓ)
    ((DirectMeasurement.registerCoordinates a n ℓ).symm (AdaptedExecution.initial a n ℓ))
    (0 : Fin (2^n)) R
  rw [reindexNamed_workGates] at hh
  have hc : Fintype.card (DirectMeasurement.AuxWire a ℓ ⊕ Fin n)=n+3*a+2*ℓ+31 := by
    rw [Fintype.card_sum,DirectMeasurement.auxiliary_card,Fintype.card_fin]
    omega
  rw [hc,DirectMeasurement.auxiliary_card] at hh
  exact hh

theorem physicalSyntax_calls (c : PhysicalAdapter.Circuit a n ℓ) (hℓ : 0<ℓ) (R : ℕ) :
    (physicalSyntax c R).matrixCalls=R*(c.toQuery (PhysicalAdapter.gateEval a n ℓ hℓ)).matrixQueries ∧
    (physicalSyntax c R).vectorCalls=R*(c.toQuery (PhysicalAdapter.gateEval a n ℓ hℓ)).vectorQueries := by
  letI : Nonempty (DirectMeasurement.AuxWire a ℓ) := ⟨.inr ()⟩
  have hh := repeated_calls (HadamardClock.bitsFinEquiv n)
    (reindexNamed (Fintype.equivFin (PhysicalAdapter.Space a n ℓ)) c) (finiteGate a n ℓ hℓ)
    (DirectMeasurement.acceptancePattern a ℓ)
    ((DirectMeasurement.registerCoordinates a n ℓ).symm (AdaptedExecution.initial a n ℓ))
    (0 : Fin (2^n)) R
  have hc : (reindexNamed (Fintype.equivFin (PhysicalAdapter.Space a n ℓ)) c).toQuery
      (finiteGate a n ℓ hℓ)=finiteRun (c.toQuery (PhysicalAdapter.gateEval a n ℓ hℓ)) :=
    reindexNamed_toQuery _ _ c
  rw [hc] at hh
  simpa only [physicalSyntax,reindexCircuit_matrixQueries,reindexCircuit_vectorQueries] using hh

theorem query_depths (c : PhysicalAdapter.Circuit a n ℓ) (hℓ : 0<ℓ) (R : ℕ) :
    matrixDepth (lower c hℓ R)=R*(c.toQuery (PhysicalAdapter.gateEval a n ℓ hℓ)).matrixQueries ∧
    (lower c hℓ R).vectorDepth=R*(c.toQuery (PhysicalAdapter.gateEval a n ℓ hℓ)).vectorQueries := by
  exact ⟨(CostedExecution.Program.lower_matrixCalls _ _ _ _).trans (physicalSyntax_calls c hℓ R).1,
    (CostedExecution.Program.lower_vectorCalls _ _ _ _).trans (physicalSyntax_calls c hℓ R).2⟩

theorem register_bound (c : PhysicalAdapter.Circuit a n ℓ) (hℓ : 0<ℓ) (R : ℕ) :
    RegisterBound (2^(n+3*a+2*ℓ+31)) (lower c hℓ R) := by
  rw [←PhysicalAdapter.space_card a n ℓ]
  exact CostedExecution.Program.lower_registerBound _ _ _ _

theorem instrument_depth (c : PhysicalAdapter.Circuit a n ℓ) (hℓ : 0<ℓ) (R : ℕ) :
    instrumentDepth (lower c hℓ R)=(physicalSyntax c R).cost+1 :=
  CostedExecution.Program.lower_instrumentDepth _ _ _ _

end OptimalQLS.Reduction.DirectCosted
