import OptimalQLS.Refinement.CostedExecution.RealLocality
import OptimalQLS.Refinement.PhysicalProgram.Complete

/-! # Literal tensor-frame embeddings in the common physical bit register -/
noncomputable section
namespace OptimalQLS.Refinement.CostedExecution
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
open PhysicalProgram PhysicalMeasurement
open scoped Classical
local instance : Nonempty Label := ⟨.pub⟩
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

abbrev FullWire (a n ℓ : ℕ) := AuxWire a ℓ ⊕ Fin n

def registerBits (a n ℓ : ℕ) : Register a n ℓ → FullWire a n ℓ → Bool :=
  (registerCoordinates a n ℓ).symm

def correctionQspWire (a n ℓ : ℕ) (w : Unit ⊕ QSVTWire a) : FullWire a n ℓ :=
  .inl (.inl w)

def filterQspWire (a n ℓ : ℕ) (w : Unit ⊕ QSVTWire (a+4)) : FullWire a n ℓ :=
  .inl (.inr (.inr (.inl w)))

def preparationWire (a n ℓ : ℕ) (w : PrepWire a ℓ) : FullWire a n ℓ :=
  .inl (.inr (.inl w))

def correctionQspFrame (a n ℓ : ℕ) :
    PhysicalSignal a × (Bits n × (PrepAux a ℓ × (FilterSignal a × Fin 4))) ≃ Register a n ℓ :=
  tensorFrame (Equiv.refl _) correctionWiring

def correctionQspEmbedding (a n ℓ : ℕ) :
    WireEmbedding phaseBits (registerBits a n ℓ) (correctionQspFrame a n ℓ) where
  wire := ⟨correctionQspWire a n ℓ,by intro i j h; exact Sum.inl_injective (Sum.inl_injective h)⟩
  read := by intro x r i; rfl
  outside := by
    intro x y r j hj
    rcases j with (j|j)
    · rcases j with (j|j)
      · exact False.elim (hj j rfl)
      · rfl
    · rfl

def filterQspFrame (a n ℓ : ℕ) :
    PhysicalSignal (a+4) × ((Fin 4 × Bits n) × (CorrectionSignal a × PrepAux a ℓ)) ≃ Register a n ℓ :=
  tensorFrame (Equiv.refl _) filterWiring

def filterQspEmbedding (a n ℓ : ℕ) :
    WireEmbedding phaseBits (registerBits a n ℓ) (filterQspFrame a n ℓ) where
  wire := ⟨filterQspWire a n ℓ,by
    intro i j h
    exact Sum.inl_injective (Sum.inr_injective (Sum.inr_injective (Sum.inl_injective h)))⟩
  read := by intro x r i; rfl
  outside := by
    intro x y r j hj
    rcases j with (j|j)
    · rcases j with (j|j)
      · rfl
      · rcases j with (j|j)
        · rfl
        · rcases j with (j|j)
          · exact False.elim (hj j rfl)
          · rfl
    · rfl

/-- The local oracle frame keeps signal and data columns as spectators. -/
def correctionOracleFrame (a n ℓ : ℕ) :
    OracleLocalState × ((Bits a × Bits n) × (PrepAux a ℓ × (FilterSignal a × Fin 4))) ≃ Register a n ℓ :=
  tensorFrame (oracleAttachWiring a (Bits n)) correctionWiring

def oracleSignalWire (a : ℕ) : Unit ⊕ OracleLocalWire → Unit ⊕ QSVTWire a
  | .inl u => .inl u
  | .inr (.inl i) => .inr (.inr ⟨i.val,by omega⟩)
  | .inr (.inr i) => .inr (.inr ⟨i.val+2,by omega⟩)

def correctionOracleEmbedding (a n ℓ : ℕ) :
    WireEmbedding phaseBits (registerBits a n ℓ) (correctionOracleFrame a n ℓ) := by
  apply WireEmbedding.ofWireMap (phaseCoordinates OracleLocalWire) _ _
    (fun i=>correctionQspWire a n ℓ (oracleSignalWire a i))
  · intro x r i
    rcases i with (i|(i|i))
    · rfl
    · fin_cases i <;> rfl
    · fin_cases i <;> rfl
  · intro x y r j hj
    rcases j with (j|j)
    · rcases j with (j|j)
      · rcases j with (j|(j|j))
        · exact False.elim (hj (.inl j) rfl)
        · rfl
        · fin_cases j
          · exact False.elim (hj (.inr (.inl 0)) rfl)
          · exact False.elim (hj (.inr (.inl 1)) rfl)
          · exact False.elim (hj (.inr (.inr 0)) rfl)
          · exact False.elim (hj (.inr (.inr 1)) rfl)
      · rfl
    · rfl


def prepSynthesisWire (a ℓ : ℕ) : PrepWire a ℓ := .inl (.inl ())
def prepSpareWire (a ℓ : ℕ) : PrepWire a ℓ := .inl (.inr (.inl ()))
def prepGraphWire (a ℓ : ℕ) (i : GraphSignalWire a) : PrepWire a ℓ :=
  .inl (.inr (.inr (.inl i)))
def prepLabelWire (a ℓ : ℕ) (i : Unit ⊕ Unit) : PrepWire a ℓ :=
  .inl (.inr (.inr (.inr (.inl i))))
def prepCounterWire (a ℓ : ℕ) (i : Fin ℓ ⊕ Fin ℓ) : PrepWire a ℓ :=
  .inl (.inr (.inr (.inr (.inr i))))
def prepScratchWire (a ℓ : ℕ) (i : Unit ⊕ (Unit ⊕ Unit)) : PrepWire a ℓ := .inr i

def preparationAuxFrame (a n ℓ : ℕ) :
    GateSynthesis.Space (LabelWire ℓ) ×
      ((PreparationData (Bits a) (Bits n) × PhaseScratch) × (CorrectionSignal a × FilterSignal a)) ≃
        Register a n ℓ :=
  tensorFrame (CompilerAttachment.auxFrame a n ℓ) (PhysicalProgram.preparationFrame a n ℓ)

def preparationAuxWire (a n ℓ : ℕ) : Unit ⊕ LabelWire ℓ → FullWire a n ℓ
  | .inl _ => preparationWire a n ℓ (prepSynthesisWire a ℓ)
  | .inr (.inl i) => preparationWire a n ℓ
      (prepLabelWire a ℓ (if i=0 then .inl () else .inr ()))
  | .inr (.inr i) => preparationWire a n ℓ (prepCounterWire a ℓ i)

def preparationAuxEmbedding (a n ℓ : ℕ) :
    WireEmbedding phaseBits (registerBits a n ℓ) (preparationAuxFrame a n ℓ) := by
  apply WireEmbedding.ofWireMap (phaseCoordinates (LabelWire ℓ)) _ _ (preparationAuxWire a n ℓ)
  · intro x r i
    rcases i with (i|(i|i))
    · rfl
    · fin_cases i
      · change (labelBitsEquiv (labelBitsEquiv.symm (x.2 (.inl 0),x.2 (.inl 1)))).1 = _
        rw [Equiv.apply_symm_apply]
        rfl
      · change (labelBitsEquiv (labelBitsEquiv.symm (x.2 (.inl 0),x.2 (.inl 1)))).2 = _
        rw [Equiv.apply_symm_apply]
        rfl
    · cases i <;> rfl
  · intro x y r j hj
    rcases j with (j|j)
    · rcases j with (j|j)
      · rfl
      · rcases j with (j|j)
        · rcases j with (j|j)
          · rcases j with (j|j)
            · exact False.elim (hj (.inl ()) rfl)
            · rcases j with (j|j)
              · rfl
              · rcases j with (j|j)
                · rfl
                · rcases j with (j|j)
                  · rcases j with (j|j)
                    · exact False.elim (hj (.inr (.inl 0)) (by cases j; rfl))
                    · exact False.elim (hj (.inr (.inl 1)) (by cases j; rfl))
                  · exact False.elim (hj (.inr (.inr j)) rfl)
          · rfl
        · rfl
    · rfl


def preparationOracleFrame (a n ℓ : ℕ) :
    OracleLocalState × (Bits n × (CompilerAttachment.SourceRest a ℓ ×
      (CorrectionSignal a × FilterSignal a))) ≃ Register a n ℓ :=
  tensorFrame (Equiv.refl _) (tensorFrame (CompilerAttachment.vectorFrame a n ℓ)
    (PhysicalProgram.preparationFrame a n ℓ))

def preparationOracleWire (a n ℓ : ℕ) : Unit ⊕ OracleLocalWire → FullWire a n ℓ
  | .inl _ => preparationWire a n ℓ (prepScratchWire a ℓ (.inl ()))
  | .inr (.inl i) => preparationWire a n ℓ
      (prepLabelWire a ℓ (if i=0 then .inl () else .inr ()))
  | .inr (.inr i) => preparationWire a n ℓ
      (prepScratchWire a ℓ (.inr (if i=0 then .inl () else .inr ())))

def preparationOracleEmbedding (a n ℓ : ℕ) :
    WireEmbedding phaseBits (registerBits a n ℓ) (preparationOracleFrame a n ℓ) := by
  apply WireEmbedding.ofWireMap (phaseCoordinates OracleLocalWire) _ _ (preparationOracleWire a n ℓ)
  · intro x r i
    rcases i with (i|(i|i))
    · rfl
    · fin_cases i
      · change (labelBitsEquiv (labelBitsEquiv.symm (x.2 (.inl 0),x.2 (.inl 1)))).1 = _
        rw [Equiv.apply_symm_apply]; rfl
      · change (labelBitsEquiv (labelBitsEquiv.symm (x.2 (.inl 0),x.2 (.inl 1)))).2 = _
        rw [Equiv.apply_symm_apply]; rfl
    · fin_cases i <;> rfl
  · intro x y r j hj
    rcases j with (j|j)
    · rcases j with (j|j)
      · rfl
      · rcases j with (j|j)
        · rcases j with (j|j)
          · rcases j with (j|j)
            · rfl
            · rcases j with (j|j)
              · rfl
              · rcases j with (j|j)
                · rfl
                · rcases j with (j|j)
                  · rcases j with (j|j)
                    · exact False.elim (hj (.inr (.inl 0)) (by cases j; rfl))
                    · exact False.elim (hj (.inr (.inl 1)) (by cases j; rfl))
                  · rfl
          · rcases j with (j|j)
            · exact False.elim (hj (.inl ()) (by cases j; rfl))
            · rcases j with (j|j)
              · exact False.elim (hj (.inr (.inr 0)) (by cases j; rfl))
              · exact False.elim (hj (.inr (.inr 1)) (by cases j; rfl))
        · rfl
    · rfl

/-- Graph labels are high/low, whereas the common binary chart is low-first. -/
theorem graphBits_low (h l : Bool) :
    (HadamardClock.bitsFinEquiv 2).symm (GraphEncoding.graphBits (h,l)) 0 = l := by
  cases h <;> cases l <;> rfl

theorem graphBits_high (h l : Bool) :
    (HadamardClock.bitsFinEquiv 2).symm (GraphEncoding.graphBits (h,l)) 1 = h := by
  cases h <;> cases l <;> rfl

def graphDataWire (a n ℓ : ℕ) (i : Fin 2) : FullWire a n ℓ :=
  .inl (.inr (.inr (.inr i)))

def preparationGraphFrame (a n ℓ : ℕ) :
    GraphLocalState × ((Bits a × Bits n) × (CompilerAttachment.CompilerRest ℓ ×
      (CorrectionSignal a × FilterSignal a))) ≃ Register a n ℓ :=
  tensorFrame (Equiv.refl _) (tensorFrame (CompilerAttachment.graphFrame a n ℓ)
    (PhysicalProgram.preparationFrame a n ℓ))

def preparationGraphWire (a n ℓ : ℕ) : Unit ⊕ GraphLocalWire → FullWire a n ℓ
  | .inl _ => preparationWire a n ℓ (prepScratchWire a ℓ (.inl ()))
  | .inr (.inl (.inl i)) => preparationWire a n ℓ
      (prepLabelWire a ℓ (if i=0 then .inl () else .inr ()))
  | .inr (.inl (.inr none)) => preparationWire a n ℓ (prepGraphWire a ℓ (.inl ()))
  | .inr (.inl (.inr (some i))) =>
      if i=0 then preparationWire a n ℓ (prepGraphWire a ℓ (.inr (.inl ()))) else
      if i=1 then preparationWire a n ℓ (prepGraphWire a ℓ (.inr (.inr (.inl ())))) else
      if i=2 then graphDataWire a n ℓ 1 else
      if i=3 then graphDataWire a n ℓ 0 else
        preparationWire a n ℓ (prepGraphWire a ℓ (.inr (.inr (.inr (.inl ())))))
  | .inr (.inr i) => preparationWire a n ℓ
      (prepScratchWire a ℓ (.inr (if i=0 then .inl () else .inr ())))

def preparationGraphEmbedding (a n ℓ : ℕ) :
    WireEmbedding phaseBits (registerBits a n ℓ) (preparationGraphFrame a n ℓ) := by
  apply WireEmbedding.ofWireMap (phaseCoordinates GraphLocalWire) _ _ (preparationGraphWire a n ℓ)
  · intro x r i
    rcases i with (i|((i|(_|i))|i))
    · rfl
    · fin_cases i
      · change (labelBitsEquiv (labelBitsEquiv.symm (x.2 (.inl (.inl 0)),x.2 (.inl (.inl 1))))).1 = _
        rw [Equiv.apply_symm_apply]; rfl
      · change (labelBitsEquiv (labelBitsEquiv.symm (x.2 (.inl (.inl 0)),x.2 (.inl (.inl 1))))).2 = _
        rw [Equiv.apply_symm_apply]; rfl
    · rfl
    · fin_cases i
      · rfl
      · rfl
      · exact graphBits_high _ _
      · exact graphBits_low _ _
      · rfl
    · fin_cases i <;> rfl
  · intro x y r j hj
    rcases j with (j|j)
    · rcases j with (j|j)
      · rfl
      · rcases j with (j|j)
        · rcases j with (j|j)
          · rcases j with (j|j)
            · rfl
            · rcases j with (j|j)
              · rfl
              · rcases j with (j|j)
                · rcases j with (j|(j|(j|(j|j))))
                  · exact False.elim (hj (.inr (.inl (.inr none))) (by cases j; rfl))
                  · exact False.elim (hj (.inr (.inl (.inr (some 0)))) (by cases j; rfl))
                  · exact False.elim (hj (.inr (.inl (.inr (some 1)))) (by cases j; rfl))
                  · exact False.elim (hj (.inr (.inl (.inr (some 4)))) (by cases j; rfl))
                  · rfl
                · rcases j with (j|j)
                  · rcases j with (j|j)
                    · exact False.elim (hj (.inr (.inl (.inl 0))) (by cases j; rfl))
                    · exact False.elim (hj (.inr (.inl (.inl 1))) (by cases j; rfl))
                  · rfl
          · rcases j with (j|j)
            · exact False.elim (hj (.inl ()) (by cases j; rfl))
            · rcases j with (j|j)
              · exact False.elim (hj (.inr (.inr 0)) (by cases j; rfl))
              · exact False.elim (hj (.inr (.inr 1)) (by cases j; rfl))
        · rcases j with (j|j)
          · rfl
          · fin_cases j
            · exact False.elim (hj (.inr (.inl (.inr (some 3)))) rfl)
            · exact False.elim (hj (.inr (.inl (.inr (some 2)))) rfl)
    · rfl


def filterGraphFrame (a n ℓ : ℕ) :
    GraphLocalState × ((Bits a × Bits n) × (CorrectionSignal a × PrepAux a ℓ)) ≃ Register a n ℓ :=
  tensorFrame (graphAttachWiring a (Bits n)) filterWiring

def filterGraphWire (a n ℓ : ℕ) : Unit ⊕ GraphLocalWire → FullWire a n ℓ
  | .inl _ => filterQspWire a n ℓ (.inl ())
  | .inr (.inl (.inl i)) => filterQspWire a n ℓ (.inr (.inr ⟨i.val,by omega⟩))
  | .inr (.inl (.inr none)) => filterQspWire a n ℓ (.inr (.inl ⟨0,by omega⟩))
  | .inr (.inl (.inr (some i))) =>
      if i=0 then filterQspWire a n ℓ (.inr (.inl ⟨1,by omega⟩)) else
      if i=1 then filterQspWire a n ℓ (.inr (.inl ⟨2,by omega⟩)) else
      if i=2 then graphDataWire a n ℓ 1 else
      if i=3 then graphDataWire a n ℓ 0 else
        filterQspWire a n ℓ (.inr (.inl ⟨3,by omega⟩))
  | .inr (.inr i) => filterQspWire a n ℓ (.inr (.inr ⟨i.val+2,by omega⟩))

def filterGraphEmbedding (a n ℓ : ℕ) :
    WireEmbedding phaseBits (registerBits a n ℓ) (filterGraphFrame a n ℓ) := by
  apply WireEmbedding.ofWireMap (phaseCoordinates GraphLocalWire) _ _ (filterGraphWire a n ℓ)
  · intro x r i
    rcases i with (i|((i|(_|i))|i))
    · rfl
    · fin_cases i <;> rfl
    · rfl
    · fin_cases i
      · rfl
      · rfl
      · exact graphBits_high _ _
      · exact graphBits_low _ _
      · rfl
    · fin_cases i <;> rfl
  · intro x y r j hj
    rcases j with (j|j)
    · rcases j with (j|j)
      · rfl
      · rcases j with (j|j)
        · rfl
        · rcases j with (j|j)
          · rcases j with (j|(j|j))
            · exact False.elim (hj (.inl ()) (by cases j; rfl))
            · revert hj
              refine Fin.cases (fun hj=>?_) (fun j hj=>?_) j
              · exact False.elim (hj (.inr (.inl (.inr none))) rfl)
              · revert hj
                refine Fin.cases (fun hj=>?_) (fun j hj=>?_) j
                · exact False.elim (hj (.inr (.inl (.inr (some 0)))) rfl)
                · revert hj
                  refine Fin.cases (fun hj=>?_) (fun j hj=>?_) j
                  · exact False.elim (hj (.inr (.inl (.inr (some 1)))) rfl)
                  · revert hj
                    refine Fin.cases (fun hj=>?_) (fun j hj=>?_) j
                    · exact False.elim (hj (.inr (.inl (.inr (some 4)))) rfl)
                    · rfl
            · fin_cases j
              · exact False.elim (hj (.inr (.inl (.inl 0))) rfl)
              · exact False.elim (hj (.inr (.inl (.inl 1))) rfl)
              · exact False.elim (hj (.inr (.inr 0)) rfl)
              · exact False.elim (hj (.inr (.inr 1)) rfl)
          · fin_cases j
            · exact False.elim (hj (.inr (.inl (.inr (some 3)))) rfl)
            · exact False.elim (hj (.inr (.inl (.inr (some 2)))) rfl)
    · rfl

def preparationReflectionFrame (a n ℓ : ℕ) :
    CompilerAttachment.ReflectionState n × (CompilerAttachment.ReflectionRest a ℓ ×
      (CorrectionSignal a × FilterSignal a)) ≃ Register a n ℓ :=
  tensorFrame (CompilerAttachment.reflectionFrame a n ℓ) (PhysicalProgram.preparationFrame a n ℓ)

def preparationReflectionWire (a n ℓ : ℕ) : Unit ⊕ CompilerAttachment.ReflectionWire n → FullWire a n ℓ
  | .inl _ => preparationWire a n ℓ (prepScratchWire a ℓ (.inl ()))
  | .inr (.inl (.inl i)) =>
      if i=0 then preparationWire a n ℓ (prepLabelWire a ℓ (.inl ())) else
      if i=1 then preparationWire a n ℓ (prepLabelWire a ℓ (.inr ())) else
      if i=2 then graphDataWire a n ℓ 1 else graphDataWire a n ℓ 0
  | .inr (.inl (.inr i)) => .inr i
  | .inr (.inr i) => preparationWire a n ℓ
      (prepScratchWire a ℓ (.inr (if i=0 then .inl () else .inr ())))

def preparationReflectionEmbedding (a n ℓ : ℕ) :
    WireEmbedding phaseBits (registerBits a n ℓ) (preparationReflectionFrame a n ℓ) := by
  apply WireEmbedding.ofWireMap (phaseCoordinates (CompilerAttachment.ReflectionWire n)) _ _
    (preparationReflectionWire a n ℓ)
  · intro x r i
    rcases i with (i|((i|i)|i))
    · rfl
    · fin_cases i
      · change (labelBitsEquiv (labelBitsEquiv.symm (x.2 (.inl (.inl 0)),x.2 (.inl (.inl 1))))).1 = _
        rw [Equiv.apply_symm_apply]; rfl
      · change (labelBitsEquiv (labelBitsEquiv.symm (x.2 (.inl (.inl 0)),x.2 (.inl (.inl 1))))).2 = _
        rw [Equiv.apply_symm_apply]; rfl
      · exact graphBits_high _ _
      · exact graphBits_low _ _
    · rfl
    · fin_cases i <;> rfl
  · intro x y r j hj
    rcases j with (j|j)
    · rcases j with (j|j)
      · rfl
      · rcases j with (j|j)
        · rcases j with (j|j)
          · rcases j with (j|j)
            · rfl
            · rcases j with (j|j)
              · rfl
              · rcases j with (j|j)
                · rfl
                · rcases j with (j|j)
                  · rcases j with (j|j)
                    · exact False.elim (hj (.inr (.inl (.inl 0))) (by cases j; rfl))
                    · exact False.elim (hj (.inr (.inl (.inl 1))) (by cases j; rfl))
                  · rfl
          · rcases j with (j|j)
            · exact False.elim (hj (.inl ()) (by cases j; rfl))
            · rcases j with (j|j)
              · exact False.elim (hj (.inr (.inr 0)) (by cases j; rfl))
              · exact False.elim (hj (.inr (.inr 1)) (by cases j; rfl))
        · rcases j with (j|j)
          · rfl
          · fin_cases j
            · exact False.elim (hj (.inr (.inl (.inl 3))) rfl)
            · exact False.elim (hj (.inr (.inl (.inl 2))) rfl)
    · exact False.elim (hj (.inr (.inl (.inr j))) rfl)

end OptimalQLS.Refinement.CostedExecution
