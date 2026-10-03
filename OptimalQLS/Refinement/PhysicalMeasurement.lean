import OptimalQLS.Refinement.PhysicalProgram.Frames
import OptimalQLS.Refinement.Repetition.PhysicalRefinement

/-! # Literal bit measurement and reset on the complete physical run register -/
noncomputable section
namespace OptimalQLS.Refinement.PhysicalMeasurement
open Matrix TransducerCompiler BinaryClock PolynomialTransform PhysicalProgram
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

private def boolBits : Bool ≃ (Unit → Bool) where
  toFun b := fun _=>b
  invFun b := b ()
  left_inv _ := rfl
  right_inv b := by funext i; cases i; rfl

/-- Product association maps each existing bit literally; it is not a gate. -/
def productBits {A B I J : Type*} (e : A ≃ (I → Bool)) (f : B ≃ (J → Bool)) :
    A × B ≃ (I ⊕ J → Bool) where
  toFun p := Sum.elim (e p.1) (f p.2)
  invFun b := (e.symm (fun i=>b (.inl i)),f.symm (fun j=>b (.inr j)))
  left_inv p := by rcases p with ⟨a,b⟩; simp
  right_inv b := by funext i; cases i <;> simp

abbrev QWire (a : ℕ) := Unit ⊕ QSVTWire a
abbrev GraphSignalWire (a : ℕ) := Unit ⊕ (Unit ⊕ (Unit ⊕ (Unit ⊕ Fin a)))
abbrev CoarseWire (a ℓ : ℕ) := Unit ⊕ (Unit ⊕ (GraphSignalWire a ⊕ ((Unit ⊕ Unit) ⊕ (Fin ℓ ⊕ Fin ℓ))))
abbrev PrepWire (a ℓ : ℕ) := CoarseWire a ℓ ⊕ (Unit ⊕ (Unit ⊕ Unit))
abbrev AuxWire (a ℓ : ℕ) := QWire a ⊕ (PrepWire a ℓ ⊕ (QWire (a+4) ⊕ Fin 2))

def qCoordinates (a : ℕ) : PolynomialTransform.PhysicalSignal a ≃ (QWire a → Bool) :=
  productBits boolBits (Equiv.refl _)

def graphSignalCoordinates (a : ℕ) : GraphEncoding.PhysicalSignal (Bits a) ≃ (GraphSignalWire a → Bool) :=
  productBits boolBits (productBits boolBits (productBits boolBits (productBits boolBits (Equiv.refl _))))

def coarseCoordinates (a ℓ : ℕ) : CoarseAux (GraphEncoding.PhysicalSignal (Bits a)) ℓ ≃ (CoarseWire a ℓ → Bool) :=
  productBits boolBits (productBits boolBits (productBits (graphSignalCoordinates a)
    (productBits (labelBitsEquiv.trans (productBits boolBits boolBits))
      (productBits (Equiv.refl _) (Equiv.refl _)))))

def prepCoordinates (a ℓ : ℕ) : PrepAux a ℓ ≃ (PrepWire a ℓ → Bool) :=
  productBits (coarseCoordinates a ℓ) (productBits boolBits (productBits boolBits boolBits))

abbrev AuxState (a ℓ : ℕ) := CorrectionSignal a × (PrepAux a ℓ × (FilterSignal a × Fin 4))

def auxCoordinates (a ℓ : ℕ) : AuxState a ℓ ≃ (AuxWire a ℓ → Bool) :=
  productBits (qCoordinates a) (productBits (prepCoordinates a ℓ)
    (productBits (qCoordinates (a+4)) (HadamardClock.bitsFinEquiv 2).symm))

def splitRegister (a n ℓ : ℕ) : Register a n ℓ ≃ AuxState a ℓ × Bits n where
  toFun p := ((p.1,(p.2.1,(p.2.2.1,p.2.2.2.1))),p.2.2.2.2)
  invFun p := (p.1.1,(p.1.2.1,(p.1.2.2.1,(p.1.2.2.2,p.2))))
  left_inv _ := rfl
  right_inv _ := rfl

def registerCoordinates (a n ℓ : ℕ) : (AuxWire a ℓ ⊕ Fin n → Bool) ≃ Register a n ℓ :=
  (productBits (auxCoordinates a ℓ) (Equiv.refl (Bits n))).symm.trans (splitRegister a n ℓ).symm

def acceptancePattern (a ℓ : ℕ) : AuxWire a ℓ → Bool :=
  auxCoordinates a ℓ (physicalZero a,(prepZero a ℓ,(physicalZero (a+4),2)))

def dataIndex (a n ℓ : ℕ) (x : Bits n) : Register a n ℓ :=
  (physicalZero a,(prepZero a ℓ,(physicalZero (a+4),(2,x))))

theorem registerCoordinates_accept (a n ℓ : ℕ) (x : Bits n) :
    registerCoordinates a n ℓ
      (Repetition.Physical.auxEmbedding (acceptancePattern a ℓ) x)=dataIndex a n ℓ x := by
  change (splitRegister a n ℓ).symm
    ((auxCoordinates a ℓ).symm (auxCoordinates a ℓ _),x)=_
  rw [Equiv.symm_apply_apply]
  rfl

def finiteRegisterCoordinates (a n ℓ : ℕ) : (AuxWire a ℓ ⊕ Fin n → Bool) ≃ Fin (Fintype.card (Register a n ℓ)) :=
  (registerCoordinates a n ℓ).trans (Fintype.equivFin _)

def acceptanceEmbedding (a n ℓ : ℕ) : Fin (2^n) ↪ Fin (Fintype.card (Register a n ℓ)) :=
  Repetition.reindexEmbedding (finiteRegisterCoordinates a n ℓ) (HadamardClock.bitsFinEquiv n)
    (Repetition.Physical.auxEmbedding (acceptancePattern a ℓ))

theorem acceptanceEmbedding_apply (a n ℓ : ℕ) (i : Fin (2^n)) :
    acceptanceEmbedding a n ℓ i=Fintype.equivFin (Register a n ℓ)
      (dataIndex a n ℓ ((HadamardClock.bitsFinEquiv n).symm i)) := by
  simp only [acceptanceEmbedding,Repetition.reindexEmbedding,finiteRegisterCoordinates,
    Function.Embedding.coeFn_mk,Equiv.trans_apply,registerCoordinates_accept]

/-- The exact Kraus matrix of one accepting program branch is the actual product
of single-qubit auxiliary measurements followed by coherent data extraction. -/
theorem acceptance_is_bit_measurement (a n ℓ : ℕ) :
    (Repetition.Physical.auxAccept (Data := Fin n) (acceptancePattern a ℓ) *
      Repetition.Physical.auxMeasurement (acceptancePattern a ℓ)).submatrix
        (HadamardClock.bitsFinEquiv n).symm (finiteRegisterCoordinates a n ℓ).symm=
    Repetition.acceptMatrix (acceptanceEmbedding a n ℓ) :=
  Repetition.Physical.physicalAccept_reindex _ _ _

/-- Each rejected branch is a literal full bit measurement and classically
selected X gates resetting to the same all-zero initialized workspace. -/
theorem rejection_is_bit_reset (a n ℓ : ℕ) (observed : AuxWire a ℓ ⊕ Fin n → Bool) :
    (Repetition.Physical.physicalReject (acceptancePattern a ℓ)
      ((registerCoordinates a n ℓ).symm (initial a n ℓ)) observed).submatrix
        (finiteRegisterCoordinates a n ℓ).symm (finiteRegisterCoordinates a n ℓ).symm=
    Repetition.resetMatrix (acceptanceEmbedding a n ℓ)
      (Fintype.equivFin _ (initial a n ℓ)) (finiteRegisterCoordinates a n ℓ observed) := by
  have h := Repetition.Physical.physicalReject_reindex (finiteRegisterCoordinates a n ℓ)
    (HadamardClock.bitsFinEquiv n) (acceptancePattern a ℓ)
    ((registerCoordinates a n ℓ).symm (initial a n ℓ)) observed
  simpa only [finiteRegisterCoordinates,Equiv.trans_apply,Equiv.apply_symm_apply] using h

theorem auxiliary_count (a ℓ : ℕ) : Fintype.card (AuxWire a ℓ)=3*a+2*ℓ+27 := by
  simp [AuxWire,QWire,PrepWire,CoarseWire,GraphSignalWire,QSVTWire,Fintype.card_sum]
  omega

theorem all_wire_count (a n ℓ : ℕ) : Fintype.card (AuxWire a ℓ ⊕ Fin n)=n+3*a+2*ℓ+27 := by
  rw [Fintype.card_sum,auxiliary_count,Fintype.card_fin]
  omega

/-- A bound on the actually proved measurement/reset lists across all attempts,
including final failure cleanup; no coordinate predicate is priced as free. -/
theorem repetition_measure_reset_bound (a n ℓ : ℕ) :
    72000*(Fintype.card (AuxWire a ℓ)+2*Fintype.card (AuxWire a ℓ ⊕ Fin n))+
      2*Fintype.card (AuxWire a ℓ ⊕ Fin n)≤220000*(n+3*a+2*ℓ+27) := by
  rw [auxiliary_count,all_wire_count]
  omega

end OptimalQLS.Refinement.PhysicalMeasurement
