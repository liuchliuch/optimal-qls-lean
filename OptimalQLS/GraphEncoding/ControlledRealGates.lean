import OptimalQLS.GraphEncoding.ControlledGates

/-! # All controlled graph macro instructions are real elementary gates -/
noncomputable section
set_option synthInstance.maxSize 2048
namespace OptimalQLS.GraphEncoding
open Matrix TransducerCompiler PolynomialTransform DirtyAncilla Preparation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def RealPhaseGate (g : PhaseGate ι) : Prop := ∀ i j, (g.eval.val i j).im=0

theorem controlledTarget_real (U : Matrix.unitaryGroup Bool ℂ)
    (hU : ∀ i j, (U.val i j).im=0) (i j : Bool × Bool) :
    ((controlledTargetUnitary U).val i j).im=0 := by
  rw [controlledTarget_entries]
  split_ifs <;> first | exact hU _ _ | rfl

theorem realPhaseGate_real (g : TransducerCompiler.GateSynthesis.LowerGate ι) :
    RealPhaseGate (PhaseGate.real g) := g.eval_real

theorem realPhaseGate_controlledTarget (f t : ι) (hft : f≠t)
    (U : Matrix.unitaryGroup Bool ℂ) (hU : ∀ i j, (U.val i j).im=0) :
    RealPhaseGate (.pair f t hft (controlledTargetUnitary U)) := by
  intro i j
  exact TransducerCompiler.GateSynthesis.placeHom_real _ _ (controlledTarget_real U hU) i j

theorem zeroControlledTarget_gate_real (n : ℕ) (f : SmallWire n → ι)
    (hf : Function.Injective f) (t : ι) (hft : f (smallTarget n)≠t)
    (U : Matrix.unitaryGroup Bool ℂ) (hU : ∀ i j, (U.val i j).im=0)
    (g : PhaseGate ι) (hg : g ∈ zeroControlledTarget n f hf t hft U) : RealPhaseGate g := by
  simp only [zeroControlledTarget,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with (hg|hg)|hg
  · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hg
    exact realPhaseGate_real r
  · subst g
    exact realPhaseGate_controlledTarget _ _ _ U hU
  · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hg
    exact realPhaseGate_real r

theorem maskedTarget_gate_real (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (t : ι) (hft : f (smallTarget n)≠t) (mask : Fin n → Bool)
    (U : Matrix.unitaryGroup Bool ℂ) (hU : ∀ i j, (U.val i j).im=0)
    (g : PhaseGate ι) (hg : g ∈ maskedTarget n f hf t hft mask U) : RealPhaseGate g := by
  simp only [maskedTarget,List.mem_append] at hg
  rcases hg with (hg|hg)|hg
  · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hg
    exact realPhaseGate_real r
  · exact zeroControlledTarget_gate_real n f hf t hft U hU g hg
  · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hg
    exact realPhaseGate_real r

theorem TargetGate.code_real (mask : Bool × Bool) (g : TargetGate)
    (p : PhaseGate ControlledGraphWire) (hp : p ∈ g.code mask) : RealPhaseGate p := by
  cases g with
  | plain t U => exact maskedTarget_gate_real _ _ _ _ _ _ _ (fun _ _ => rfl) p hp
  | controlled c t hct b U => exact maskedTarget_gate_real _ _ _ _ _ _ _ (fun _ _ => rfl) p hp

theorem GraphWorkGate.controlledCode_real (mask : Bool × Bool) (g : GraphWorkGate)
    (p : PhaseGate ControlledGraphWire) (hp : p ∈ g.controlledCode mask) :
    RealPhaseGate p ∧ p.arity≤2 :=
  ⟨g.targetGate.code_real mask p hp,p.arity_le_two⟩

end OptimalQLS.GraphEncoding
