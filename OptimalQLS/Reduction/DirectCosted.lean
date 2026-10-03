import OptimalQLS.Reduction.DirectMeasurement
import OptimalQLS.Refinement.CostedExecution.ResourceAttachment

/-! # A costed physical program for any substituted original-oracle word

The construction is generic in the word and retry count. It measures the
existing auxiliary bits, the literal dilation head and the shared scratch.
-/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.Reduction.DirectCosted
open Matrix TransducerCompiler BinaryClock PolynomialTransform PhysicalPadding
open Refinement Refinement.Repetition LowerBounds CostedExecution
variable {a n ℓ : ℕ}

def finiteGate (a n ℓ : ℕ) (hℓ : 0<ℓ) (g : PhysicalAdapter.Gate a n ℓ) :=
  rewireUnitary (Fintype.equivFin (PhysicalAdapter.Space a n ℓ)) (PhysicalAdapter.gateEval a n ℓ hℓ g)

def physicalSyntax (c : PhysicalAdapter.Circuit a n ℓ) (R : ℕ) :
    CostedExecution.Program (PhysicalAdapter.Gate a n ℓ) (Bits a × Bits n) (Bits n)
      (DirectMeasurement.AuxWire a ℓ) (Fin n) (Fintype.card (PhysicalAdapter.Space a n ℓ)) :=
  repeated (HadamardClock.bitsFinEquiv n)
    (reindexNamed (Fintype.equivFin (PhysicalAdapter.Space a n ℓ)) c)
    (DirectMeasurement.acceptancePattern a ℓ)
    ((DirectMeasurement.registerCoordinates a n ℓ).symm (AdaptedExecution.initial a n ℓ))
    (0 : Fin (2^n)) R

def lower (c : PhysicalAdapter.Circuit a n ℓ) (hℓ : 0<ℓ) (R : ℕ) :=
  (physicalSyntax c R).lower (DirectMeasurement.finiteCoordinates a n ℓ)
    (HadamardClock.bitsFinEquiv n) (finiteGate a n ℓ hℓ)

def compressed (c : PhysicalAdapter.Circuit a n ℓ) (hℓ : 0<ℓ) (R : ℕ) :=
  repeatProgram (finiteRun (c.toQuery (PhysicalAdapter.gateEval a n ℓ hℓ)))
    (finiteAccept (DirectExecution.acceptance a n ℓ))
    (AdaptedExecution.initialIndex a n ℓ) (0 : Fin (2^n)) R

attribute [local irreducible] repeatProgram repeated CostedExecution.Program.lower

/-- Equality includes all failure outputs and all input states, not just the
promised initial basis vector. -/
theorem refines (c : PhysicalAdapter.Circuit a n ℓ) (hℓ : 0<ℓ) (R : ℕ)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (select : Bool → Bool) (v : Fin (Fintype.card (PhysicalAdapter.Space a n ℓ)) → ℂ) :
    (lower c hℓ R).executeDensity UA Ub select v=(compressed c hℓ R).executeDensity UA Ub select v := by
  have hh := repeated_refines (DirectMeasurement.finiteCoordinates a n ℓ)
    (HadamardClock.bitsFinEquiv n) (finiteGate a n ℓ hℓ) UA Ub select
    (reindexNamed (Fintype.equivFin (PhysicalAdapter.Space a n ℓ)) c)
    (DirectMeasurement.acceptancePattern a ℓ)
    ((DirectMeasurement.registerCoordinates a n ℓ).symm (AdaptedExecution.initial a n ℓ))
    (0 : Fin (2^n)) R v
  have hc : (reindexNamed (Fintype.equivFin (PhysicalAdapter.Space a n ℓ)) c).toQuery
      (finiteGate a n ℓ hℓ)=finiteRun (c.toQuery (PhysicalAdapter.gateEval a n ℓ hℓ)) :=
    reindexNamed_toQuery _ _ c
  rw [hc] at hh
  simpa only [den,lower,physicalSyntax,compressed,finiteGate,finiteRun,
    DirectMeasurement.acceptance_exact,DirectMeasurement.finiteCoordinates,Equiv.trans_apply,
    Equiv.apply_symm_apply,AdaptedExecution.initialIndex] using hh

theorem success_eq (c : PhysicalAdapter.Circuit a n ℓ) (hℓ : 0<ℓ) (R : ℕ)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (v : Fin (Fintype.card (PhysicalAdapter.Space a n ℓ)) → ℂ) :
    (lower c hℓ R).successProbability UA Ub v=(compressed c hℓ R).successProbability UA Ub v := by
  simp only [FiniteOracleProgram.successProbability,refines]

theorem output_eq (c : PhysicalAdapter.Circuit a n ℓ) (hℓ : 0<ℓ) (R : ℕ)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (v : Fin (Fintype.card (PhysicalAdapter.Space a n ℓ)) → ℂ) :
    (lower c hℓ R).conditionalOutput UA Ub v=(compressed c hℓ R).conditionalOutput UA Ub v := by
  simp only [FiniteOracleProgram.conditionalOutput,success_eq,refines]

end OptimalQLS.Reduction.DirectCosted
