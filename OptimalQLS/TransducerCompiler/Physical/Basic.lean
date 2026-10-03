import OptimalQLS.TransducerCompiler.CompleteTheorems
import OptimalQLS.Preparation.CompilerAttachment.ClockGates
import OptimalQLS.Preparation.CompilerAttachment.LocalOracle
import OptimalQLS.Refinement.CostedExecution.LocalityCore
import OptimalQLS.Reduction.Circuits

/-! Physical registers and an explicit supplied controlled-work gate list. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
open scoped Classical
namespace OptimalQLS.TransducerCompiler.Physical
open Matrix BinaryClock PolynomialTransform
open Refinement.PhysicalMeasurement (productBits)
open Refinement.CostedExecution (WireEmbedding IsTwoLocal boolCoordinates)

abbrev WorkSpace (m : ℕ) := Bool × Base (Bits m)
abbrev WorkWire (m : ℕ) := Unit ⊕ (Fin m ⊕ (Unit ⊕ Unit))
abbrev ScratchWire := Unit ⊕ (Unit ⊕ Unit)
abbrev Space (m ℓ : ℕ) := SynthSpace (Bits m) ℓ × PhaseScratch
abbrev Wire (m ℓ : ℕ) :=
  (Unit ⊕ ((Fin m ⊕ (Unit ⊕ Unit)) ⊕ (Fin ℓ ⊕ Fin ℓ))) ⊕ ScratchWire

def labelCoordinates : Label ≃ ((Unit ⊕ Unit) → Bool) :=
  labelBitsEquiv.trans (productBits boolCoordinates boolCoordinates)

def workCoordinates (m : ℕ) : WorkSpace m ≃ (WorkWire m → Bool) :=
  productBits boolCoordinates (productBits (Equiv.refl _) labelCoordinates)

def coordinates (m ℓ : ℕ) : Space m ℓ ≃ (Wire m ℓ → Bool) :=
  productBits (productBits boolCoordinates
    (productBits (productBits (Equiv.refl _) labelCoordinates)
      (productBits (Equiv.refl _) (Equiv.refl _))))
    (productBits boolCoordinates (productBits boolCoordinates boolCoordinates))

/-- An input circuit leaf explicitly supplies its at-most-two-qubit unitary,
literal selected wires and spectator tensor factor. No whole-work matrix is
counted as an elementary gate. -/
structure LocalGate {P W : Type} [Fintype P] [DecidableEq P]
    (chart : P ≃ (W → Bool)) where
  arity : ℕ
  bound : arity≤2
  Rest : Type
  [finiteRest : Fintype Rest]
  [decidableRest : DecidableEq Rest]
  frame : (Bits arity × Rest) ≃ P
  wires : WireEmbedding (Equiv.refl (Bits arity)) chart frame
  unitary : Matrix.unitaryGroup (Bits arity) ℂ

attribute [instance] LocalGate.finiteRest LocalGate.decidableRest

def LocalGate.eval {P W : Type} [Fintype P] [DecidableEq P]
    {chart : P ≃ (W → Bool)} (g : LocalGate chart) : Matrix.unitaryGroup P ℂ :=
  GateSynthesis.placeHom g.frame g.unitary

theorem LocalGate.local {P W : Type} [Fintype P] [DecidableEq P]
    {chart : P ≃ (W → Bool)} (g : LocalGate chart) : IsTwoLocal chart g.eval :=
  .tensor (by simpa using g.bound) (Equiv.refl (Bits g.arity)) g.frame g.wires g.unitary

def localEval {P W : Type} [Fintype P] [DecidableEq P]
    {chart : P ≃ (W → Bool)} : List (LocalGate chart) → Matrix.unitaryGroup P ℂ
  | [] => 1
  | g::c => localEval c*g.eval

abbrev WorkCircuit (m : ℕ) := List (LocalGate (workCoordinates m))

def ControlledWork {m : ℕ} (S : Matrix.unitaryGroup (Base (Bits m)) ℂ) (c : WorkCircuit m) : Prop :=
  localEval c=(Reduction.bitControlPort (Base (Bits m))).apply S

def clean (m ℓ : ℕ) (x : SynthSpace (Bits m) ℓ) : Space m ℓ := (x,(false,false,false))

theorem clean_isometry (m ℓ : ℕ) :
    (basisInsertion (clean m ℓ))ᴴ*basisInsertion (clean m ℓ)=1 :=
  basisInsertion_isometry _ (fun _ _ he=>congrArg Prod.fst he)

abbrev CacheRest (ℓ : ℕ) (hℓ : 0<ℓ) := {i : Fin ℓ // i≠⟨0,hℓ⟩} → Bool
abbrev WorkRest (ℓ : ℕ) (hℓ : 0<ℓ) := Bool × (Bits ℓ × (CacheRest ℓ hℓ × PhaseScratch))

/-- The supplied control wire is the actual first cache bit, with every other
clock/cache/synthesis/data wire retained in its original location. -/
def workFrame (m ℓ : ℕ) (hℓ : 0<ℓ) : WorkSpace m × WorkRest ℓ hℓ ≃ Space m ℓ where
  toFun p := ((p.2.1,(p.1.2,(p.2.2.1,
    (Equiv.funSplitAt (⟨0,hℓ⟩ : Fin ℓ) Bool).symm (p.1.1,p.2.2.2.1)))),p.2.2.2.2)
  invFun p := ((p.1.2.2.2 ⟨0,hℓ⟩,p.1.2.1),
    (p.1.1,(p.1.2.2.1,((fun i=>p.1.2.2.2 i),p.2))))
  left_inv p := by
    rcases p with ⟨⟨b,d,l⟩,z,t,r,s⟩
    simp only [Equiv.funSplitAt,Equiv.piSplitAt,Equiv.coe_fn_symm_mk,dite_true]
    congr 4
    funext i
    simp [i.property]
  right_inv p := by
    rcases p with ⟨⟨z,⟨d,l⟩,t,c⟩,s⟩
    change ((z,((d,l),(t,(Equiv.funSplitAt (⟨0,hℓ⟩ : Fin ℓ) Bool).symm
      ((Equiv.funSplitAt (⟨0,hℓ⟩ : Fin ℓ) Bool) c)))),s)=((z,((d,l),(t,c))),s)
    rw [Equiv.symm_apply_apply]

def workWire (m ℓ : ℕ) (hℓ : 0<ℓ) : WorkWire m ↪ Wire m ℓ where
  toFun
    | .inl _ => .inl (.inr (.inr (.inr ⟨0,hℓ⟩)))
    | .inr i => .inl (.inr (.inl i))
  inj' := by
    intro i j he
    rcases i with i|i <;> rcases j with j|j <;> simp_all

def workEmbedding (m ℓ : ℕ) (hℓ : 0<ℓ) :
    WireEmbedding (workCoordinates m) (coordinates m ℓ) (workFrame m ℓ hℓ) where
  wire := workWire m ℓ hℓ
  read := by
    intro x r i
    cases i with
    | inl i => simp [workWire,coordinates,workFrame,workCoordinates,productBits,boolCoordinates,
        Equiv.funSplitAt_symm_apply]
    | inr i => rfl
  outside := by
    intro x y r j hj
    rcases j with (j|(j|j))|j
    · rfl
    · exact False.elim (hj (.inr j) rfl)
    · rcases j with j|j
      · rfl
      · have hn : j≠⟨0,hℓ⟩ := by intro he; subst j; exact hj (.inl ()) rfl
        simp [coordinates,workFrame,productBits,Equiv.funSplitAt_symm_apply,hn]
    · rfl

theorem placed_work_local (m ℓ : ℕ) (hℓ : 0<ℓ) (g : LocalGate (workCoordinates m)) :
    IsTwoLocal (coordinates m ℓ) (GateSynthesis.placeHom (workFrame m ℓ hℓ) g.eval) :=
  IsTwoLocal.place _ (workEmbedding m ℓ hℓ) _ g.local

end OptimalQLS.TransducerCompiler.Physical
