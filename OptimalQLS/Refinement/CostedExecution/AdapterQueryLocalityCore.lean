import OptimalQLS.Refinement.CostedExecution.QueryLocalityCore

/-! # Argument-register placement for the adapter's original oracle queries -/
noncomputable section
namespace OptimalQLS.Refinement.CostedExecution
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
open PhysicalProgram PhysicalMeasurement Reduction PhysicalAdapter
open scoped Classical
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

/-- An exact controlled original-UA tensor, before assigning physical wires. -/
def adapterOriginalMatrixFrame (a n ℓ : ℕ) (f : PhysicalProgram.Flag) :
    ControlFrame (originalMatrixPort a n ℓ f) :=
  (singleFlagFrame (A := Bits a × Bits n) (smallTarget 2)).lift
    (scratchPort (matrixWiring a n ℓ f)) (fun _=>rfl)

/-- The source macro's original-Ub query uses the existing external flag. -/
def adapterOriginalVectorFrame (a n ℓ : ℕ) : ControlFrame (originalVectorPort a n ℓ) :=
  (singleFlagFrame (A := Bits n) (.inl 0 : DilationWire)).lift
    (scratchPort (vectorWiring a n ℓ)) (fun _=>rfl)

theorem adapterOriginalMatrixFrame_apply (a n ℓ : ℕ) (f : PhysicalProgram.Flag)
    (v : Bool × (Bits a × Bits n)) (r : (adapterOriginalMatrixFrame a n ℓ f).Rest) :
    (adapterOriginalMatrixFrame a n ℓ f).wiring (v,r)=
      adapterMatrixFrame a n ℓ f
        ((r.1.1,(Equiv.funSplitAt (smallTarget 2) Bool).symm (v.1,r.1.2)),
          (v.2,(Fintype.equivFin (PhysicalAdapter.matrixFrame a n ℓ f).Rest).symm r.2)) := rfl

theorem adapterOriginalVectorFrame_apply (a n ℓ : ℕ)
    (v : Bool × Bits n) (r : (adapterOriginalVectorFrame a n ℓ).Rest) :
    (adapterOriginalVectorFrame a n ℓ).wiring (v,r)=
      adapterVectorFrame a n ℓ
        ((r.1.1,(Equiv.funSplitAt (.inl 0 : DilationWire) Bool).symm (v.1,r.1.2)),
          (v.2,(Fintype.equivFin (PhysicalAdapter.vectorFrame a n ℓ).Rest).symm r.2)) := rfl

def adapterOriginalMatrixWire (a n ℓ : ℕ) (f : PhysicalProgram.Flag) :
    Unit ⊕ (Fin a ⊕ Fin n) → AdapterWire a n ℓ
  | .inl _ => .inr (.inr (.inl ()))
  | .inr (.inl i) => .inl (normalizedSignalWire a (n+1) ℓ f i)
  | .inr (.inr i) => .inl (.inr i.succ)

theorem adapterOriginalMatrixWire_injective (a n ℓ : ℕ) (f : PhysicalProgram.Flag) :
    Function.Injective (adapterOriginalMatrixWire a n ℓ f) := by
  intro i j hij
  cases f <;> rcases i with (i|(i|i)) <;> rcases j with (j|(j|j)) <;>
    simp_all [adapterOriginalMatrixWire,normalizedSignalWire,
      preparationWire,prepGraphWire,filterQspWire,correctionQspWire]

def adapterOriginalVectorWire (a n ℓ : ℕ) : Unit ⊕ Fin n → AdapterWire a n ℓ
  | .inl _ => .inl (controlWire a (n+1) ℓ .preparation)
  | .inr i => .inl (.inr i.succ)

theorem adapterOriginalVectorWire_injective (a n ℓ : ℕ) : Function.Injective (adapterOriginalVectorWire a n ℓ) := by
  intro i j hij
  rcases i with (i|i) <;> rcases j with (j|j) <;>
    simp_all [adapterOriginalVectorWire,controlWire]

macro "adapter_query_wire" : tactic => `(tactic| (simp only [adapterOriginalMatrixWire,adapterOriginalVectorWire]; query_wire))

end OptimalQLS.Refinement.CostedExecution
