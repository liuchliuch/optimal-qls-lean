import OptimalQLS.KernelReflectionPhysical.Query
import OptimalQLS.Refinement.CostedExecution.QueryLocalityCore

/-! # Literal tensor placements for every emitted kernel-transducer gate -/
noncomputable section
namespace OptimalQLS.KernelReflectionPhysical
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
open Preparation.WorkGates Refinement.CostedExecution
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 16384
set_option linter.unusedSimpArgs false

variable {D J : Type} [Fintype D] [DecidableEq D]

/-- Physical bit coordinates: synthesis, labels, signal, control, scratch and data. -/
def physicalBits {a : ℕ} (d : D → J → Bool) (x : Physical a D) :
    (Unit ⊕ Wire (LogicalWire a)) ⊕ J → Bool := Sum.elim (phaseBits x.1) (d x.2)

/-- The same coordinate map is a complete computational-basis equivalence when
D is a literal data-bit register. -/
def physicalCoordinates (a n : ℕ) : Physical a (Bits n) ≃
    (((Unit ⊕ Wire (LogicalWire a)) ⊕ Fin n) → Bool) :=
  Refinement.PhysicalMeasurement.productBits (phaseCoordinates _) (Equiv.refl _)

@[simp] theorem physicalCoordinates_apply (a n : ℕ) (x : Physical a (Bits n)) :
    physicalCoordinates a n x=physicalBits (fun d : Bits n=>d) x := rfl

theorem physical_register_bits (a n : ℕ) :
    Fintype.card ((Unit ⊕ Wire (LogicalWire a)) ⊕ Fin n)=a+n+7 := by
  simp [Preparation.WorkGates.Wire,Preparation.WorkGates.LogicalWire,Fintype.card_sum]
  omega

def workEmbedding (a : ℕ) (d : D → J → Bool) :
    WireEmbedding phaseBits (physicalBits (a := a) d) (Equiv.refl (Physical a D)) where
  wire := Function.Embedding.inl
  read := by intros; rfl
  outside := by
    intro x y r j hj
    cases j with
    | inl j => exact False.elim (hj j rfl)
    | inr j => rfl

theorem workGate_local (a : ℕ) (d : D → J → Bool)
    (g : PhaseGate (Wire (LogicalWire a))) :
    IsTwoLocal (physicalBits d) (elementaryPlacement (D := D) g.eval) :=
  IsTwoLocal.place _ (workEmbedding a d) _ (phase_leaf_local g)

/-- The active oracle-adapter wires are literal named physical bits. -/
def queryWire (a : ℕ) : Unit ⊕ OracleLocalWire →
    (Unit ⊕ Wire (LogicalWire a)) ⊕ J
  | .inl _ => .inl (.inl ())
  | .inr (.inl i) => .inl (.inr (.inl (.inl (if i=0 then 1 else 2))))
  | .inr (.inr i) => .inl (.inr (.inr i))

theorem queryWire_injective (a : ℕ) : Function.Injective (queryWire (J := J) a) := by
  intro i j hij
  rcases i with i|(i|i) <;> rcases j with j|(j|j)
  all_goals try { simp [queryWire] at hij; subst_vars; rfl }
  all_goals fin_cases i <;> fin_cases j <;> simp_all [queryWire]

def queryGateFrame (a : ℕ) (D : Type) :
    OracleLocalState × ((Bits a × D) × (Bool × Bool)) ≃ Physical a D :=
  tensorFrame (Equiv.refl _) (queryFrame a D)

def queryEmbedding (a : ℕ) (d : D → J → Bool) :
    WireEmbedding phaseBits (physicalBits (a := a) d) (queryGateFrame a D) where
  wire := ⟨queryWire a,queryWire_injective a⟩
  read := by
    intro x r i
    rcases i with i|(i|i)
    · cases i; rfl
    · fin_cases i <;>
        simp [queryWire,physicalBits,phaseBits,queryGateFrame,tensorFrame,queryFrame,
          Preparation.CompilerAttachment.scratchFrame,querySourceFrame,registerEquiv,
          logicalEquiv,oracleLocalWiring]
    · fin_cases i <;> rfl
  outside := by
    intro x y r j hj
    rcases j with (j|(j|j))|j
    · cases j
      exact False.elim (hj (.inl ()) rfl)
    · rcases j with j|(j|j)
      · fin_cases j
        · simp [physicalBits,phaseBits,queryGateFrame,tensorFrame,queryFrame,
            Preparation.CompilerAttachment.scratchFrame,querySourceFrame,registerEquiv,
            logicalEquiv,oracleLocalWiring]
        · exact False.elim (hj (.inr (.inl 0)) rfl)
        · exact False.elim (hj (.inr (.inl 1)) rfl)
      · rfl
      · rfl
    · exact False.elim (hj (.inr (.inr j)) rfl)
    · rfl

theorem queryGate_local (a : ℕ) (d : D → J → Bool) (g : PhaseGate OracleLocalWire) :
    IsTwoLocal (physicalBits d) (queryGateEval (D := D) a g) := by
  rw [queryGateEval,elementaryPlacement,placeHom_comp]
  exact IsTwoLocal.place _ (queryEmbedding a d) _ (phase_leaf_local g)

/-- Realness survives a literal tensor placement, including arbitrary data spectators. -/
theorem placeHom_real {L R P : Type*} [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R] [Fintype P] [DecidableEq P]
    (e : L × R ≃ P) (U : Matrix.unitaryGroup L ℂ)
    (h : ∀ i j, (U.val i j).im=0) :
    ∀ i j, ((GateSynthesis.placeHom e U).val i j).im=0 := by
  intro i j
  rw [GraphEncoding.placeHom_entries]
  split_ifs <;> simp [h]

theorem workGate_real (a : ℕ) (g : PhaseGate (Wire (LogicalWire a))) (hg : RealGate g) :
    ∀ i j, ((elementaryPlacement (D := D) g.eval).val i j).im=0 :=
  placeHom_real _ _ hg

theorem queryGate_real (a : ℕ) (g : PhaseGate OracleLocalWire)
    (hg : GraphEncoding.RealPhaseGate g) :
    ∀ i j, ((queryGateEval (D := D) a g).val i j).im=0 :=
  placeHom_real _ _ (placeHom_real _ _ hg)

end OptimalQLS.KernelReflectionPhysical
