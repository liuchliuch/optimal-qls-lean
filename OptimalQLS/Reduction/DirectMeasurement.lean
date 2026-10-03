import OptimalQLS.Reduction.DirectExecution
import OptimalQLS.Refinement.CostedExecution.Attachment

/-! # Physical bits for joint acceptance, including the literal dilation head -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.Reduction.DirectMeasurement
open Matrix TransducerCompiler BinaryClock PolynomialTransform PhysicalPadding
open Refinement Refinement.Repetition LowerBounds
open PhysicalMeasurement (productBits)

abbrev ScratchWire := Unit ⊕ (Unit ⊕ Unit)
abbrev AuxWire (a ℓ : ℕ) := (PhysicalMeasurement.AuxWire a ℓ ⊕ ScratchWire) ⊕ Unit

def boolCoordinates : Bool ≃ (Unit → Bool) where
  toFun b := fun _=>b
  invFun b := b ()
  left_inv _ := rfl
  right_inv b := by funext i; cases i; rfl

def scratchCoordinates : PhaseScratch ≃ (ScratchWire → Bool) :=
  productBits boolCoordinates (productBits boolCoordinates boolCoordinates)

def regroup (a n ℓ : ℕ) : PhysicalAdapter.Space a n ℓ ≃
    ((PhysicalMeasurement.AuxState a ℓ × PhaseScratch) × Bool) × Bits n where
  toFun p := (((((PhysicalMeasurement.splitRegister a (n+1) ℓ) p.1).1,p.2),
      p.1.2.2.2.2 0),fun i=>p.1.2.2.2.2 i.succ)
  invFun p := ((PhysicalMeasurement.splitRegister a (n+1) ℓ).symm
      (p.1.1.1,Fin.cases p.1.2 p.2),p.1.1.2)
  left_inv p := by
    rcases p with ⟨x,r⟩
    change ((PhysicalMeasurement.splitRegister a (n+1) ℓ).symm
      (((PhysicalMeasurement.splitRegister a (n+1) ℓ) x).1,
        (PhysicalAdapter.headTail n).symm ((PhysicalAdapter.headTail n)
          ((PhysicalMeasurement.splitRegister a (n+1) ℓ) x).2)),r)=(x,r)
    rw [Equiv.symm_apply_apply,Prod.mk.eta,Equiv.symm_apply_apply]
  right_inv p := by rcases p with ⟨⟨⟨x,r⟩,b⟩,d⟩; rfl

def auxCoordinates (a ℓ : ℕ) :
    (PhysicalMeasurement.AuxState a ℓ × PhaseScratch) × Bool ≃ (AuxWire a ℓ → Bool) :=
  productBits (productBits (PhysicalMeasurement.auxCoordinates a ℓ) scratchCoordinates) boolCoordinates

def registerCoordinates (a n ℓ : ℕ) : (AuxWire a ℓ ⊕ Fin n → Bool) ≃ PhysicalAdapter.Space a n ℓ :=
  (productBits (auxCoordinates a ℓ) (Equiv.refl (Bits n))).symm.trans (regroup a n ℓ).symm

def finiteCoordinates (a n ℓ : ℕ) : (AuxWire a ℓ ⊕ Fin n → Bool) ≃
    Fin (Fintype.card (PhysicalAdapter.Space a n ℓ)) :=
  (registerCoordinates a n ℓ).trans (Fintype.equivFin _)

def acceptancePattern (a ℓ : ℕ) : AuxWire a ℓ → Bool :=
  Sum.elim (Sum.elim (PhysicalMeasurement.acceptancePattern a ℓ) (fun _=>false)) (fun _=>true)

theorem register_accept (a n ℓ : ℕ) (x : Bits n) :
    registerCoordinates a n ℓ (Repetition.Physical.auxEmbedding (acceptancePattern a ℓ) x)=
      PhysicalAdapter.clean a n ℓ (PhysicalMeasurement.dataIndex a (n+1) ℓ (Fin.cases true x)) := by
  change ((PhysicalMeasurement.splitRegister a (n+1) ℓ).symm
    ((PhysicalMeasurement.auxCoordinates a ℓ).symm
      ((PhysicalMeasurement.auxCoordinates a ℓ)
        (physicalZero a,(PhysicalProgram.prepZero a ℓ,(physicalZero (a+4),2)))),
      Fin.cases true x),(false,false,false))=_
  rw [Equiv.symm_apply_apply]
  rfl

theorem acceptance_apply (a n ℓ : ℕ) (i : Fin (2^n)) :
    DirectExecution.acceptance a n ℓ i=
      PhysicalAdapter.clean a n ℓ (PhysicalMeasurement.dataIndex a (n+1) ℓ
        (Fin.cases true ((HadamardClock.bitsFinEquiv n).symm i))) := by
  change PhysicalAdapter.clean a n ℓ (PhysicalMeasurement.dataIndex a (n+1) ℓ
    ((HadamardClock.bitsFinEquiv (n+1)).symm ((extractionCoordinates n) (.inr i))))=_
  simp only [extractionCoordinates,Equiv.trans_apply,Equiv.symm_apply_apply]
  rfl

theorem acceptance_exact (a n ℓ : ℕ) :
    finiteAccept (DirectExecution.acceptance a n ℓ)=
      Repetition.reindexEmbedding (finiteCoordinates a n ℓ) (HadamardClock.bitsFinEquiv n)
        (Repetition.Physical.auxEmbedding (acceptancePattern a ℓ)) := by
  apply Function.Embedding.ext
  intro i
  change Fintype.equivFin _ (DirectExecution.acceptance a n ℓ i)=
    Fintype.equivFin _ (registerCoordinates a n ℓ
      (Repetition.Physical.auxEmbedding (acceptancePattern a ℓ) ((HadamardClock.bitsFinEquiv n).symm i)))
  rw [register_accept,acceptance_apply]

theorem auxiliary_card (a ℓ : ℕ) : Fintype.card (AuxWire a ℓ)=3*a+2*ℓ+31 := by
  rw [Fintype.card_sum,Fintype.card_sum,PhysicalMeasurement.auxiliary_count]
  have hs : Fintype.card ScratchWire=3 := by decide
  rw [hs,Fintype.card_unit]

end OptimalQLS.Reduction.DirectMeasurement
