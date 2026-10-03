import OptimalQLS.PolynomialTransform.CleanEmbedding

/-! # Physical signal wires: two QSVT labels and three reusable scratch bits -/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Matrix DirtyAncilla OptimalQLS.TransducerCompiler

abbrev QSVTWire (a : ℕ) := Fin a ⊕ Fin 4
abbrev LogicalSignal (a : ℕ) := (Bool × Bool) × (Fin a → Bool)
abbrev PhysicalSignal (a : ℕ) := GateSynthesis.Space (QSVTWire a)
abbrev PhaseScratch := Bool × (Bool × Bool)

def averageWire (a : ℕ) : QSVTWire a := .inr 0
def dilationWire (a : ℕ) : QSVTWire a := .inr 1
def flagWire (a : ℕ) : QSVTWire a := .inr 2
def borrowedWire (a : ℕ) : QSVTWire a := .inr 3

/-- Only register rearrangement: the three scratch bits remain explicit. -/
def physicalSignalEquiv (a : ℕ) : LogicalSignal a × PhaseScratch ≃ PhysicalSignal a where
  toFun p := (p.2.1,fun i => match i with
    | .inl j => p.1.2 j
    | .inr j => if j=0 then p.1.1.1 else if j=1 then p.1.1.2 else
      if j=2 then p.2.2.1 else p.2.2.2)
  invFun b := (((b.2 (.inr 0),b.2 (.inr 1)),fun i => b.2 (.inl i)),
    b.1,b.2 (.inr 2),b.2 (.inr 3))
  left_inv p := by rcases p with ⟨⟨⟨u,v⟩,x⟩,s,f,r⟩; simp
  right_inv b := by
    apply Prod.ext
    · rfl
    · funext i; cases i with
      | inl i => rfl
      | inr i => fin_cases i <;> simp

def physicalCleanSignal (a : ℕ) (x : LogicalSignal a) : PhysicalSignal a :=
  physicalSignalEquiv a (x,(false,false,false))

theorem physicalCleanSignal_injective (a : ℕ) : Function.Injective (physicalCleanSignal a) := by
  intro x y h
  exact congrArg Prod.fst ((physicalSignalEquiv a).injective h)

/-- All data coordinates are spectators of the scratch-register arrangement. -/
def physicalEquiv (a : ℕ) (D : Type*) :
    (LogicalSignal a × D) × PhaseScratch ≃ PhysicalSignal a × D where
  toFun p := (physicalSignalEquiv a (p.1.1,p.2),p.1.2)
  invFun p := ((((physicalSignalEquiv a).symm p.1).1,p.2),((physicalSignalEquiv a).symm p.1).2)
  left_inv p := by rcases p with ⟨⟨l,d⟩,s⟩; simp
  right_inv p := by rcases p with ⟨s,d⟩; simp

def physicalClean (a : ℕ) {D : Type*} (x : LogicalSignal a × D) : PhysicalSignal a × D :=
  (physicalCleanSignal a x.1,x.2)

/-- The zero-test's only non-control wires are the shared flag and borrowed bit. -/
def phaseWiring (a : ℕ) : SmallWire a → QSVTWire a
  | .inl i => .inl i
  | .inr i => .inr ⟨i.val+2,by omega⟩

theorem phaseWiring_injective (a : ℕ) : Function.Injective (phaseWiring a) := by
  intro i j h
  cases i <;> cases j <;> simp only [phaseWiring,Sum.inl.injEq,Sum.inr.injEq,
    Sum.inl_ne_inr,Sum.inr_ne_inl,Fin.ext_iff] at h ⊢ <;> omega

theorem average_ne_phase_target (a : ℕ) : averageWire a ≠ phaseWiring a (smallTarget a) := by
  simp [averageWire,phaseWiring,smallTarget]

def physicalPhaseCode (a : ℕ) (branch : Bool) (z w : Circle) : List (PhaseGate (QSVTWire a)) :=
  controlledPhaseMacro a (phaseWiring a) (phaseWiring_injective a)
    (averageWire a) (average_ne_phase_target a)
    (fun b => if b.1=branch then if b.2 then z else w else 1)

def logicalPhaseFunction (a : ℕ) (branch : Bool) (z w : Circle) : LogicalSignal a → Circle :=
  fun x => if x.1.1=branch then if x.2=(fun _ => false) then z else w else 1

theorem physicalPhaseCode_length (a : ℕ) (branch : Bool) (z w : Circle) :
    (physicalPhaseCode a branch z w).length ≤ 781*(a+1) :=
  controlledPhaseMacro_length ..

/-- Exact phase semantics on all computational signal labels; all scratch is restored. -/
theorem physicalPhaseCode_basis (a : ℕ) (branch : Bool) (z w : Circle) (x : LogicalSignal a) :
    (phaseEval (physicalPhaseCode a branch z w)).val *ᵥ
      Pi.single (physicalCleanSignal a x) (1 : ℂ)=
      (logicalPhaseFunction a branch z w x : ℂ) •
        (Pi.single (physicalCleanSignal a x) 1 : PhysicalSignal a → ℂ) := by
  have h := controlledPhaseMacro_basis a (phaseWiring a) (phaseWiring_injective a)
    (averageWire a) (average_ne_phase_target a)
    (fun b => if b.1=branch then if b.2 then z else w else 1)
    (physicalCleanSignal a x).2 (by simp [physicalCleanSignal,physicalSignalEquiv,phaseWiring,smallTarget])
  have he : (∀ i : Fin a, x.2 i=false) ↔ x.2=(fun _ => false) := funext_iff.symm
  simpa [physicalPhaseCode,physicalCleanSignal,physicalSignalEquiv,phaseWiring,averageWire,
    logicalPhaseFunction,he] using h

theorem physical_signal_cardinality (a : ℕ) : Fintype.card (PhysicalSignal a)=2^(a+5) := by
  simp [PhysicalSignal,GateSynthesis.Space,GateSynthesis.Data,QSVTWire,Fintype.card_prod,
    Fintype.card_fun,pow_add]
  ring

end OptimalQLS.PolynomialTransform
