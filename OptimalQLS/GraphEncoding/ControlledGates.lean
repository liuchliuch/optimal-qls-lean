import OptimalQLS.GraphEncoding.MaskedTarget
import OptimalQLS.GraphEncoding.AllowedCalls

/-! # Constant-size named-wire code for masked graph primitives -/
noncomputable section
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 1000000
namespace OptimalQLS.GraphEncoding
attribute [local instance] Classical.propDecidable
open Matrix TransducerCompiler
open PolynomialTransform DirtyAncilla Preparation

/-- none is the graph's globally borrowed Toffoli bit. The five remaining
positions are SELECT, edge dilation, graph high, graph low, oracle dilation. -/
abbrev CoreWire := Option (Fin 5)
abbrev MaskCoreWire := Fin 2 ⊕ CoreWire
/-- The final two data wires are the zero-test flag and its dirty borrowed bit.
The extra outer Bool in GateSynthesis.Space is the clean synthesis bit. -/
abbrev ControlledGraphWire := MaskCoreWire ⊕ Fin 2

def coreWire (i : CoreWire) : ControlledGraphWire := .inl (.inr i)
def maskWire (i : Fin 2) : ControlledGraphWire := .inl (.inl i)
def flagWire : ControlledGraphWire := .inr 0
def dirtyWire : ControlledGraphWire := .inr 1

def controlsTwo : SmallWire 2 → ControlledGraphWire
  | .inl i => maskWire i
  | .inr i => .inr i

def controlsThree (c : CoreWire) : SmallWire 3 → ControlledGraphWire
  | .inl i => ![maskWire 0,maskWire 1,coreWire c] i
  | .inr i => .inr i

theorem controlsTwo_injective : Function.Injective controlsTwo := by
  intro i j h
  cases i <;> cases j <;> simp_all [controlsTwo, maskWire]

theorem controlsThree_injective (c : CoreWire) : Function.Injective (controlsThree c) := by
  intro i j h
  rcases i with i|i <;> rcases j with j|j
  · fin_cases i <;> fin_cases j <;> simp_all [controlsThree, maskWire, coreWire]
  · fin_cases i <;> simp_all [controlsThree, maskWire, coreWire]
  · fin_cases j <;> simp_all [controlsThree, maskWire, coreWire]
  · simpa [controlsThree] using h

theorem controlsTwo_flag_ne (t : CoreWire) : controlsTwo (smallTarget 2) ≠ coreWire t := by simp [controlsTwo, smallTarget, coreWire]

theorem controlsThree_flag_ne (c t : CoreWire) : controlsThree c (smallTarget 3) ≠ coreWire t := by simp [controlsThree, smallTarget, coreWire]

theorem controlsTwo_target_ne (t : CoreWire) (i : Fin 2) : controlsTwo (.inl i) ≠ coreWire t := by simp [controlsTwo, maskWire, coreWire]

theorem controlsThree_target_ne (c t : CoreWire) (hct : c≠t) (i : Fin 3) :
    controlsThree c (.inl i) ≠ coreWire t := by
  fin_cases i <;> simp_all [controlsThree, maskWire, coreWire]

/-- Every actual graph primitive is one target unitary with at most one
pre-existing literal control. -/
inductive TargetGate where
  | plain (target : CoreWire) (U : Matrix.unitaryGroup Bool ℝ)
  | controlled (control target : CoreWire) (distinct : control≠target)
      (polarity : Bool) (U : Matrix.unitaryGroup Bool ℝ)

def TargetGate.code (mask : Bool × Bool) : TargetGate → List (PhaseGate ControlledGraphWire)
  | .plain t U => maskedTarget 2 controlsTwo controlsTwo_injective (coreWire t)
      (controlsTwo_flag_ne t) ![mask.1,mask.2] (complexifyRealUnitary U)
  | .controlled c t hct p U => maskedTarget 3 (controlsThree c) (controlsThree_injective c)
      (coreWire t) (controlsThree_flag_ne c t) ![mask.1,mask.2,p] (complexifyRealUnitary U)

theorem TargetGate.code_length (mask : Bool × Bool) (g : TargetGate) : (g.code mask).length ≤ 3214 := by
  cases g with
  | plain t U => exact maskedTarget_length 2 (by omega) _ _ _ _ _ _
  | controlled c t hct p U => exact maskedTarget_length 3 (by omega) _ _ _ _ _ _

def TargetGate.target : TargetGate → CoreWire
  | .plain t _ => t
  | .controlled _ t _ _ _ => t

def TargetGate.unitary : TargetGate → Matrix.unitaryGroup Bool ℝ
  | .plain _ U => U
  | .controlled _ _ _ _ U => U

def TargetGate.test (g : TargetGate) (b : ControlledGraphWire → Bool) : Prop :=
  match g with
  | .plain _ _ => True
  | .controlled c _ _ p _ => b (coreWire c)=p

/-- Concrete basis action with all named scratch wires restored. -/
theorem TargetGate.code_basis (mask : Bool × Bool) (g : TargetGate)
    (b : ControlledGraphWire → Bool) (hb : b flagWire=false) :
    (phaseEval (g.code mask)).val *ᵥ Pi.single (false,b) 1 =
      ∑ y : Bool,
        (if b (maskWire 0)=mask.1 ∧ b (maskWire 1)=mask.2 ∧ g.test b
          then (complexifyRealUnitary g.unitary).val y (b (coreWire g.target))
          else if y=b (coreWire g.target) then 1 else 0) •
        (Pi.single (false,Function.update b (coreWire g.target) y) 1 :
          TransducerCompiler.GateSynthesis.Space ControlledGraphWire → ℂ) := by
  classical
  cases g with
  | plain t U =>
    have hh := maskedTarget_basis 2 controlsTwo controlsTwo_injective (coreWire t)
      (controlsTwo_flag_ne t) (controlsTwo_target_ne t) ![mask.1,mask.2]
      (complexifyRealUnitary U) b hb
    simpa [TargetGate.code, TargetGate.test, TargetGate.target, TargetGate.unitary,
      controlsTwo, Fin.forall_fin_succ, maskWire] using hh
  | controlled c t hct p U =>
    have hh := maskedTarget_basis 3 (controlsThree c) (controlsThree_injective c)
      (coreWire t) (controlsThree_flag_ne c t) (controlsThree_target_ne c t hct)
      ![mask.1,mask.2,p] (complexifyRealUnitary U) b hb
    simpa [TargetGate.code, TargetGate.test, TargetGate.target, TargetGate.unitary,
      controlsThree, Fin.forall_fin_succ, and_assoc] using hh

/-- The four reversible label positions occupy these named core wires. -/
def labelCore (i : Fin 4) : CoreWire := some i.castSucc

theorem labelCore_injective : Function.Injective labelCore := by
  intro i j h
  exact (Fin.castSucc_injective 4) (Option.some.inj h)

theorem labelCore_ne_borrowed (i : Fin 4) : labelCore i ≠ none := by simp [labelCore]

def edgeTarget : TransducerCompiler.GateSynthesis.LowerGate (Fin 4) → TargetGate
  | .x t => .plain (labelCore t) RealToffoli.xReal
  | .cx c t hct => .controlled (labelCore c) (labelCore t)
      (fun h => hct (labelCore_injective h)) true RealToffoli.xReal
  | .template c d t _ _ _ (.atom (.rotate θ)) => .plain none (RealToffoli.rotationReal θ)
  | .template c d t _ _ _ (.atom .controlA) =>
      .controlled (labelCore c) none (labelCore_ne_borrowed c) true RealToffoli.xReal
  | .template c d t _ _ _ (.atom .controlB) =>
      .controlled (labelCore d) none (labelCore_ne_borrowed d) true RealToffoli.xReal
  | .template c d t _ _ _ .copy =>
      .controlled none (labelCore t) (Ne.symm (labelCore_ne_borrowed t)) true RealToffoli.xReal

def GraphWorkGate.targetGate : GraphWorkGate → TargetGate
  | .selectBit U => .plain (some 0) U
  | .controlledHadamard => .controlled (some 0) (some 4) (by decide) false
      (mixReal (-halfAmplitude) halfAmplitude_bound)
  | .controlledX => .controlled (some 0) (some 4) (by decide) false RealToffoli.xReal
  | .edge g => edgeTarget g

def GraphWorkGate.controlledCode (mask : Bool × Bool) (g : GraphWorkGate) :
    List (PhaseGate ControlledGraphWire) := g.targetGate.code mask

theorem GraphWorkGate.controlledCode_length (mask : Bool × Bool) (g : GraphWorkGate) :
    (g.controlledCode mask).length ≤ 3214 := g.targetGate.code_length mask

end OptimalQLS.GraphEncoding
