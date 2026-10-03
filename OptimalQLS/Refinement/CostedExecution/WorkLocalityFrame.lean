import OptimalQLS.Refinement.CostedExecution.LocalityFrames

/-! # The raw work frame is a literal wire regrouping

The nonlinear compiler-label permutation is already an emitted gate word. This
file verifies that the frame itself cancels that permutation on every column,
including arbitrary values of all three reusable scratch bits. -/
noncomputable section
namespace OptimalQLS.Refinement.CostedExecution
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
open PhysicalProgram PhysicalMeasurement CompilerAttachment
open scoped Classical
local instance : Nonempty Label := ⟨.pub⟩
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

/-- Full-space version of the clean-input raw-register identity. -/
theorem workRegisterEquiv_raw (a : ℕ) (D : Type) (b : Bool) (l : Label)
    (s : Bits a) (c : Bool) (d : D) (z f r : Bool) :
    workRegisterEquiv a D ((((b,(s,d)),l),c),(z,f,r)) =
      ((z,Sum.elim (rawLogical b l s c) (fun i=>if i=0 then f else r)),d) := by
  cases b <;> cases l <;> rfl

def workSourceBits {a : ℕ} {D : Type}
    (x : GateSynthesis.Space (WorkGates.Wire (WorkGates.LogicalWire a))) (d : D) :
    WorkSource a D :=
  (((x.2 (.inl (.inl 0)),((fun i=>x.2 (.inl (.inr (.inl i)))),d)),
    labelBitsEquiv.symm (x.2 (.inl (.inl 2)),x.2 (.inl (.inl 1)))),
    x.2 (.inl (.inr (.inr ()))))

def workScratchBits {a : ℕ}
    (x : GateSynthesis.Space (WorkGates.Wire (WorkGates.LogicalWire a))) : PhaseScratch :=
  (x.1,x.2 (.inr 0),x.2 (.inr 1))

theorem workRegisterEquiv_inverse (a : ℕ) (D : Type)
    (x : GateSynthesis.Space (WorkGates.Wire (WorkGates.LogicalWire a))) (d : D) :
    (workRegisterEquiv a D).symm (x,d) = (workSourceBits x d,workScratchBits x) := by
  apply (workRegisterEquiv a D).injective
  rw [Equiv.apply_symm_apply]
  change (x,d) = workRegisterEquiv a D
    ((((x.2 (.inl (.inl 0)),((fun i=>x.2 (.inl (.inr (.inl i)))),d)),
      labelBitsEquiv.symm (x.2 (.inl (.inl 2)),x.2 (.inl (.inl 1)))),
      x.2 (.inl (.inr (.inr ())))),(x.1,x.2 (.inr 0),x.2 (.inr 1)))
  rw [workRegisterEquiv_raw]
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext i
      rcases i with ((i|(i|i))|i)
      · fin_cases i <;>
          simp [rawLogical,compilerBitEquiv,Equiv.apply_symm_apply]
      · rfl
      · cases i; rfl
      · fin_cases i <;> rfl
  · rfl

def preparationWorkFrame (a n ℓ : ℕ) :
    GateSynthesis.Space (WorkGates.Wire (WorkGates.LogicalWire (a+4))) ×
      ((Fin 4 × Bits n) × (WorkRest ℓ × (CorrectionSignal a × FilterSignal a))) ≃
        Register a n (ℓ+1) :=
  tensorFrame (Equiv.refl _) (tensorFrame (workFrame a n ℓ)
    (PhysicalProgram.preparationFrame a n (ℓ+1)))

/-- This equality exposes every source coordinate of the physical work frame. -/
theorem preparationWorkFrame_apply (a n ℓ : ℕ)
    (x : GateSynthesis.Space (WorkGates.Wire (WorkGates.LogicalWire (a+4))))
    (r : (Fin 4 × Bits n) × (WorkRest ℓ × (CorrectionSignal a × FilterSignal a))) :
    preparationWorkFrame a n ℓ (x,r) =
      PhysicalProgram.preparationFrame a n (ℓ+1)
        ((workSourceFrame a n ℓ (workSourceBits x r.1,r.2.1),workScratchBits x),r.2.2) := by
  change PhysicalProgram.preparationFrame a n (ℓ+1)
    ((workFrame a n ℓ ((x,r.1),r.2.1)),r.2.2) = _
  simp only [workFrame,Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map_apply,
    Equiv.refl_apply,workRegisterEquiv_inverse]
  rfl

def signalIndexWire (a : ℕ) : Fin (a+4) → GraphSignalWire a :=
  Fin.cases (.inl ()) (Fin.cases (.inr (.inl ()))
    (Fin.cases (.inr (.inr (.inl ())))
      (Fin.cases (.inr (.inr (.inr (.inl ()))))
        (fun i=>.inr (.inr (.inr (.inr i)))))))

def preparationWorkWire (a n ℓ : ℕ) :
    Unit ⊕ WorkGates.Wire (WorkGates.LogicalWire (a+4)) → FullWire a n (ℓ+1)
  | .inl _ => preparationWire a n (ℓ+1) (prepScratchWire a (ℓ+1) (.inl ()))
  | .inr (.inl (.inl i)) =>
      if i=0 then preparationWire a n (ℓ+1) (prepSpareWire a (ℓ+1)) else
      preparationWire a n (ℓ+1) (prepLabelWire a (ℓ+1) (if i=1 then .inr () else .inl ()))
  | .inr (.inl (.inr (.inl i))) =>
      preparationWire a n (ℓ+1) (prepGraphWire a (ℓ+1) (signalIndexWire a i))
  | .inr (.inl (.inr (.inr _))) =>
      preparationWire a n (ℓ+1) (prepCounterWire a (ℓ+1) (.inr 0))
  | .inr (.inr i) => preparationWire a n (ℓ+1)
      (prepScratchWire a (ℓ+1) (.inr (if i=0 then .inl () else .inr ())))

def preparationWorkEmbedding (a n ℓ : ℕ) :
    WireEmbedding phaseBits (registerBits a n (ℓ+1)) (preparationWorkFrame a n ℓ) := by
  apply WireEmbedding.ofWireMap
    (phaseCoordinates (WorkGates.Wire (WorkGates.LogicalWire (a+4)))) _ _ (preparationWorkWire a n ℓ)
  · intro x r i
    rw [preparationWorkFrame_apply]
    rcases i with (i|((i|(i|i))|i))
    · rfl
    · fin_cases i
      · rfl
      · change (labelBitsEquiv (labelBitsEquiv.symm (x.2 (.inl (.inl 2)),x.2 (.inl (.inl 1))))).2 = _
        rw [Equiv.apply_symm_apply]; rfl
      · change (labelBitsEquiv (labelBitsEquiv.symm (x.2 (.inl (.inl 2)),x.2 (.inl (.inl 1))))).1 = _
        rw [Equiv.apply_symm_apply]; rfl
    · refine Fin.cases ?_ (fun i=>?_) i
      · rfl
      · refine Fin.cases ?_ (fun i=>?_) i
        · rfl
        · refine Fin.cases ?_ (fun i=>?_) i
          · rfl
          · refine Fin.cases ?_ (fun i=>?_) i <;> rfl
    · cases i; rfl
    · fin_cases i <;> rfl
  · intro x y r j hj
    rw [preparationWorkFrame_apply,preparationWorkFrame_apply]
    rcases j with (j|j)
    · rcases j with (j|j)
      · rfl
      · rcases j with (j|j)
        · rcases j with (j|j)
          · rcases j with (j|j)
            · rfl
            · rcases j with (j|j)
              · exact False.elim (hj (.inr (.inl (.inl 0))) (by cases j; rfl))
              · rcases j with (j|j)
                · rcases j with (j|(j|(j|(j|j))))
                  · exact False.elim (hj (.inr (.inl (.inr (.inl 0)))) (by cases j; rfl))
                  · exact False.elim (hj (.inr (.inl (.inr (.inl 1)))) (by cases j; rfl))
                  · exact False.elim (hj (.inr (.inl (.inr (.inl 2)))) (by cases j; rfl))
                  · exact False.elim (hj (.inr (.inl (.inr (.inl 3)))) (by cases j; rfl))
                  · exact False.elim (hj (.inr (.inl (.inr (.inl j.succ.succ.succ.succ)))) rfl)
                · rcases j with (j|j)
                  · rcases j with (j|j)
                    · exact False.elim (hj (.inr (.inl (.inl 2))) (by cases j; rfl))
                    · exact False.elim (hj (.inr (.inl (.inl 1))) (by cases j; rfl))
                  · rcases j with (j|j)
                    · rfl
                    · revert hj
                      refine Fin.cases (fun hj=>?_) (fun j hj=>?_) j
                      · exact False.elim (hj (.inr (.inl (.inr (.inr ())))) rfl)
                      · rfl
          · rcases j with (j|j)
            · exact False.elim (hj (.inl ()) (by cases j; rfl))
            · rcases j with (j|j)
              · exact False.elim (hj (.inr (.inr 0)) (by cases j; rfl))
              · exact False.elim (hj (.inr (.inr 1)) (by cases j; rfl))
        · rfl
    · rfl

end OptimalQLS.Refinement.CostedExecution
