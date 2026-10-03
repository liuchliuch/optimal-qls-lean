import OptimalQLS.Reduction.DirectCosted
import OptimalQLS.Reduction.DirectLocality
import OptimalQLS.Refinement.CostedExecution.AdapterQueryLocality
import OptimalQLS.OracleSyntaxCoordinates

/-! Actual gate and full original-oracle wire placement throughout the same tree. -/
noncomputable section
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
open scoped Classical
namespace OptimalQLS.Reduction.DirectMeasurement
open Matrix TransducerCompiler BinaryClock PolynomialTransform PhysicalPadding
open Refinement CostedExecution

def matrixPlacement (a n ℓ : ℕ) (f : PhysicalProgram.Flag) :
    LiteralQueryPlacement (matrixArguments a n) (finiteCoordinates a n ℓ).symm
      (Repetition.reindexPort (Fintype.equivFin (PhysicalAdapter.Space a n ℓ))
        (PhysicalAdapter.originalMatrixPort a n ℓ f)) :=
  ((adapterMatrixPlacement a n ℓ f).wire_equiv (wireEquiv a n ℓ) (wireEquiv_read a n ℓ)).reindex
    (Fintype.equivFin (PhysicalAdapter.Space a n ℓ))

def vectorPlacement (a n ℓ : ℕ) :
    LiteralQueryPlacement (Equiv.refl (Bits n)) (finiteCoordinates a n ℓ).symm
      (Repetition.reindexPort (Fintype.equivFin (PhysicalAdapter.Space a n ℓ))
        (PhysicalAdapter.originalVectorPort a n ℓ)) :=
  ((adapterVectorPlacement a n ℓ).wire_equiv (wireEquiv a n ℓ) (wireEquiv_read a n ℓ)).reindex
    (Fintype.equivFin (PhysicalAdapter.Space a n ℓ))

end OptimalQLS.Reduction.DirectMeasurement

namespace OptimalQLS.Reduction.DirectCosted
open Matrix TransducerCompiler BinaryClock PolynomialTransform PhysicalPadding
open Refinement Repetition LowerBounds CostedExecution
variable {a n ℓ : ℕ}
attribute [local irreducible] repeated CostedExecution.Program.lower repeatProgram

def MatrixSource (c : PhysicalAdapter.Circuit a n ℓ)
    (p : QueryPort (Bits a × Bits n) (Fin (Fintype.card (PhysicalAdapter.Space a n ℓ)))) (adj : Bool) : Prop :=
  ∃ q : QueryPort (Bits a × Bits n) (PhysicalAdapter.Space a n ℓ),
    NamedInstruction.matrixCall q adj∈c ∧ p=Repetition.reindexPort (Fintype.equivFin _) q

def VectorSource (c : PhysicalAdapter.Circuit a n ℓ)
    (p : QueryPort (Bits n) (Fin (Fintype.card (PhysicalAdapter.Space a n ℓ)))) (adj : Bool) : Prop :=
  ∃ q : QueryPort (Bits n) (PhysicalAdapter.Space a n ℓ),
    NamedInstruction.vectorCall q adj∈c ∧ p=Repetition.reindexPort (Fintype.equivFin _) q

def PhysicalSafety (c : PhysicalAdapter.Circuit a n ℓ) (hℓ : 0<ℓ) (R : ℕ) : Prop :=
  (physicalSyntax c R).Allowed
    (fun g=>IsTwoLocal (DirectMeasurement.finiteCoordinates a n ℓ).symm (finiteGate a n ℓ hℓ g))
    (fun p adj=>MatrixSource c p adj ∧ Nonempty
      (LiteralQueryPlacement (matrixArguments a n) (DirectMeasurement.finiteCoordinates a n ℓ).symm p))
    (fun p adj=>VectorSource c p adj ∧ Nonempty
      (LiteralQueryPlacement (Equiv.refl (Bits n)) (DirectMeasurement.finiteCoordinates a n ℓ).symm p))

theorem physicalSyntax_safe (c : PhysicalAdapter.Circuit a n ℓ) (hℓ : 0<ℓ) (R : ℕ)
    (hc : PhysicalAdapter.Safe c) : PhysicalSafety c hℓ R := by
  unfold PhysicalSafety physicalSyntax
  apply allowed_repeated
  intro i hi
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  cases j with
  | gate g => exact (DirectMeasurement.gate_local a n ℓ hℓ g).reindex (Fintype.equivFin _)
  | matrixCall p adj =>
    refine ⟨⟨p,hj,rfl⟩,?_⟩
    obtain ⟨f,rfl⟩ := hc.2.1 p adj hj
    exact ⟨DirectMeasurement.matrixPlacement a n ℓ f⟩
  | vectorCall p adj =>
    refine ⟨⟨p,hj,rfl⟩,?_⟩
    rw [hc.2.2 p adj hj]
    exact ⟨DirectMeasurement.vectorPlacement a n ℓ⟩

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The literal primitive tree after changing only the conventional names of
the supplied oracle argument registers. Gate and measurement nodes are kept. -/
def sourceSyntax (c : PhysicalAdapter.Circuit a n ℓ) (R : ℕ)
    (ea : (Bits a × Bits n) ≃ A) (eb : Bits n ≃ B) :=
  (physicalSyntax c R).mapOracles ea eb

def CoordinateSafety (c : PhysicalAdapter.Circuit a n ℓ) (hℓ : 0<ℓ) (R : ℕ)
    (ea : (Bits a × Bits n) ≃ A) (eb : Bits n ≃ B) : Prop :=
  (sourceSyntax c R ea eb).Allowed
    (fun g=>IsTwoLocal (DirectMeasurement.finiteCoordinates a n ℓ).symm (finiteGate a n ℓ hℓ g))
    (fun p _=>Nonempty (LiteralQueryPlacement (ea.symm.trans (matrixArguments a n))
      (DirectMeasurement.finiteCoordinates a n ℓ).symm p))
    (fun p _=>Nonempty (LiteralQueryPlacement eb.symm (DirectMeasurement.finiteCoordinates a n ℓ).symm p))

theorem sourceSyntax_safe (c : PhysicalAdapter.Circuit a n ℓ) (hℓ : 0<ℓ) (R : ℕ)
    (hc : PhysicalAdapter.Safe c) (ea : (Bits a × Bits n) ≃ A) (eb : Bits n ≃ B) :
    CoordinateSafety c hℓ R ea eb := by
  unfold CoordinateSafety sourceSyntax
  apply CostedExecution.Program.mapOracles_allowed
  unfold physicalSyntax
  apply allowed_repeated
  intro i hi
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  cases j with
  | gate g => exact (DirectMeasurement.gate_local a n ℓ hℓ g).reindex (Fintype.equivFin _)
  | matrixCall p adj =>
    obtain ⟨f,rfl⟩ := hc.2.1 p adj hj
    exact ⟨(DirectMeasurement.matrixPlacement a n ℓ f).argument_equiv ea⟩
  | vectorCall p adj =>
    rw [hc.2.2 p adj hj]
    exact ⟨(DirectMeasurement.vectorPlacement a n ℓ).argument_equiv eb⟩

theorem sourceSyntax_lower (c : PhysicalAdapter.Circuit a n ℓ) (hℓ : 0<ℓ) (R : ℕ)
    (ea : (Bits a × Bits n) ≃ A) (eb : Bits n ≃ B) :
    (sourceSyntax c R ea eb).lower (DirectMeasurement.finiteCoordinates a n ℓ)
      (HadamardClock.bitsFinEquiv n) (finiteGate a n ℓ hℓ)=
      OracleCoordinates.program ea eb (lower c hℓ R) :=
  CostedExecution.Program.mapOracles_lower ea eb _ _ _ _

theorem sourceSyntax_cost (c : PhysicalAdapter.Circuit a n ℓ) (R : ℕ)
    (ea : (Bits a × Bits n) ≃ A) (eb : Bits n ≃ B) :
    (sourceSyntax c R ea eb).cost=(physicalSyntax c R).cost :=
  CostedExecution.Program.mapOracles_cost ea eb _

end OptimalQLS.Reduction.DirectCosted
