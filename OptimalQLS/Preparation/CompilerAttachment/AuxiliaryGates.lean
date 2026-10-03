import OptimalQLS.Preparation.CompilerAttachment.Frames
import OptimalQLS.Preparation.CompilerAttachment.ClockGates

/-! # Literal compiler auxiliary leaves in the common physical frame

Every original elementary compiler gate and every one-bit clock Hadamard is
placed on its original named wires.  The three new scratch bits and the data
register are spectators; the old synthesis bit is not assumed clean.
-/
noncomputable section
set_option synthInstance.maxSize 8192
open scoped Classical
namespace OptimalQLS.Preparation.CompilerAttachment
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla

/-- A phase leaf on the original compiler wires, with data and scratch retained. -/
def auxiliaryGateEval (a n ℓ : ℕ) (g : PhaseGate (LabelWire ℓ)) :
    Matrix.unitaryGroup (Physical a n ℓ) ℂ :=
  GateSynthesis.placeHom (auxFrame a n ℓ) g.eval

/-- Literal gate-list conversion; no matrix is treated as one emitted gate. -/
def auxiliaryMacro {A B : Type*} (a n ℓ : ℕ) (p : List (PhaseGate (LabelWire ℓ))) :
    NamedCircuit (PhaseGate (LabelWire ℓ)) A B (Physical a n ℓ) := p.map .gate

@[simp] theorem auxiliaryMacro_workGates {A B : Type*} (a n ℓ : ℕ)
    (p : List (PhaseGate (LabelWire ℓ))) :
    (auxiliaryMacro (A := A) (B := B) a n ℓ p).workGates = p.length := by
  induction p with
  | nil => rfl
  | cons g p ih => exact congrArg Nat.succ ih

@[simp] theorem auxiliaryMacro_queries {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (a n ℓ : ℕ) (p : List (PhaseGate (LabelWire ℓ))) :
    ((auxiliaryMacro (A := A) (B := B) a n ℓ p).toQuery (auxiliaryGateEval a n ℓ)).matrixQueries = 0 ∧
      ((auxiliaryMacro (A := A) (B := B) a n ℓ p).toQuery (auxiliaryGateEval a n ℓ)).vectorQueries = 0 := by
  induction p with
  | nil => exact ⟨rfl,rfl⟩
  | cons g p ih => exact ih

theorem auxiliaryMacro_eval {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (a n ℓ : ℕ) (p : List (PhaseGate (LabelWire ℓ)))
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    ((auxiliaryMacro a n ℓ p).toQuery (auxiliaryGateEval a n ℓ)).eval UA Ub =
      GateSynthesis.placeHom (auxFrame a n ℓ) (phaseEval p) := by
  induction p with
  | nil => simp [auxiliaryMacro, NamedCircuit.toQuery, QueryCircuit.eval, phaseEval]
  | cons g p ih =>
    simp only [auxiliaryMacro, List.map_cons, NamedCircuit.toQuery,
      NamedInstruction.toQuery, QueryCircuit.eval, QueryInstruction.eval, phaseEval, map_mul]
    exact congrArg (fun U => U * auxiliaryGateEval a n ℓ g) ih

/-- The common clean embedding adds only new spectator bits. -/
theorem auxiliaryPlacement_clean (a n ℓ : ℕ)
    (U : Matrix.unitaryGroup (GateSynthesis.Space (LabelWire ℓ)) ℂ) :
    (GateSynthesis.placeHom (auxFrame a n ℓ) U).val * basisInsertion (clean a n ℓ) =
      basisInsertion (clean a n ℓ) * (lowerAuxHom U).val := by
  exact placeHom_natural synthWiring (auxFrame a n ℓ) (clean a n ℓ)
    (fun d => (d,(false,false,false))) (fun _ _ => rfl) U

/-- An original lower gate is an actual real phase leaf, with the old synthesis
wire retained even between the individual leaves of a Toffoli expansion. -/
theorem auxiliaryElementary_intertwines (a n ℓ : ℕ)
    (g : GateSynthesis.LowerGate (LabelWire ℓ))
    (S : Matrix.unitaryGroup (Base (PreparationData (Bits a) (Bits n))) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup (PreparationData (Bits a) (Bits n)) ℂ) :
    (auxiliaryGateEval a n ℓ (.real g)).val * basisInsertion (clean a n ℓ) =
      basisInsertion (clean a n ℓ) * ((SynthInstruction.elementary g).eval S U₁ U₂).val := by
  exact auxiliaryPlacement_clean a n ℓ g.eval

/-- The whole clock layer has the precise original compiler semantics, for
both its preparation and its adjoint/unpreparation occurrence. -/
theorem auxiliaryClock_intertwines (a n ℓ : ℕ) (adj : Bool)
    (S : Matrix.unitaryGroup (Base (PreparationData (Bits a) (Bits n))) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup (PreparationData (Bits a) (Bits n)) ℂ) :
    (GateSynthesis.placeHom (auxFrame a n ℓ) (phaseEval (ClockGates.labelCode ℓ))).val *
        basisInsertion (clean a n ℓ) =
      basisInsertion (clean a n ℓ) * ((SynthInstruction.clock adj).eval S U₁ U₂).val := by
  rw [auxiliaryPlacement_clean, ClockGates.labelCode_synth_eval ℓ S U₁ U₂ adj]

theorem auxiliaryGate_real (a n ℓ : ℕ) (g : PhaseGate (LabelWire ℓ))
    (hg : ∀ i j, (g.eval.val i j).im = 0) :
    ∀ i j, ((auxiliaryGateEval a n ℓ g).val i j).im = 0 :=
  GateSynthesis.placeHom_real _ _ hg

theorem auxiliaryElementary_real (a n ℓ : ℕ) (g : GateSynthesis.LowerGate (LabelWire ℓ)) :
    ∀ i j, ((auxiliaryGateEval a n ℓ (.real g)).val i j).im = 0 :=
  auxiliaryGate_real a n ℓ _ g.eval_real

theorem auxiliaryClock_real (a n ℓ : ℕ) (g : PhaseGate (LabelWire ℓ))
    (hg : g ∈ ClockGates.labelCode ℓ) :
    ∀ i j, ((auxiliaryGateEval a n ℓ g).val i j).im = 0 :=
  auxiliaryGate_real a n ℓ _ (ClockGates.code_real _ g hg)

@[simp] theorem auxiliaryClock_length (ℓ : ℕ) : (ClockGates.labelCode ℓ).length = ℓ :=
  ClockGates.code_length _

theorem auxiliaryClock_arity (ℓ : ℕ) (g : PhaseGate (LabelWire ℓ))
    (hg : g ∈ ClockGates.labelCode ℓ) : g.arity = 1 :=
  ClockGates.code_arity _ g hg

end OptimalQLS.Preparation.CompilerAttachment
