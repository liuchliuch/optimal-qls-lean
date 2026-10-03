import OptimalQLS.GraphEncoding.CoreWiring
import OptimalQLS.GraphEncoding.EdgeBasis

/-! # Named one-qubit target semantics of every graph work gate -/
noncomputable section
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 1000000
namespace OptimalQLS.GraphEncoding
open Matrix PolynomialTransform TransducerCompiler
variable {S D : Type*} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]

def TargetGate.coreEnabled (g : TargetGate) (x : CoreWire → Bool) : Bool :=
  match g with
  | .plain _ _ => true
  | .controlled c _ _ p _ => decide (x c=p)

def TargetGate.coefficient (g : TargetGate) (x : CoreWire → Bool) (y : Bool) : ℂ :=
  if g.coreEnabled x then (complexifyRealUnitary g.unitary).val y (x g.target)
  else if y=x g.target then 1 else 0

@[simp] theorem coreLabels_read (x : CoreWire → Bool) (i : Fin 4) : coreLabels x i = x (labelCore i) := by
  fin_cases i <;> rfl

theorem core_controlled_basis (G : Matrix.unitaryGroup Bool ℝ) (x : CoreWire → Bool) (sd : S × D) :
    (borrow (TransducerCompiler.GateSynthesis.placeHom (controlledBitWiring Label (S × D))
      (complexifyRealUnitary (controlledBitReal G)))).val *ᵥ Pi.single (coreWiring S D (x,sd)) 1 =
      ∑ y : Bool, (if x (some 0) then (if y=x (some 4) then (1:ℂ) else 0)
          else (complexifyRealUnitary G).val y (x (some 4))) •
        (Pi.single (coreWiring S D (Function.update x (some 4) y,sd)) 1 :
          Bool × (BranchSpace S D ⊕ BranchSpace S D) → ℂ) := by
  rw [borrow_place]
  conv_lhs => rw [← core_dilation_input x sd]
  rw [placeHom_basis_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  cases hc : x (some 0)
  all_goals
    have hw := core_dilation_update x sd y
    simp only [hc] at hw
    simp [controlledBitReal, complexifyRealUnitary, Matrix.blockDiagonal_apply,
      Matrix.one_apply, Fintype.sum_bool, hc, hw]

theorem x_target_sum (x : CoreWire → Bool) (sd : S × D) (t : CoreWire) (c : Bool) :
    (∑ y : Bool, (if c then (complexifyRealUnitary RealToffoli.xReal).val y (x t)
          else if y=x t then 1 else 0) •
        (Pi.single (coreWiring S D (Function.update x t y,sd)) 1 :
          Bool × (BranchSpace S D ⊕ BranchSpace S D) → ℂ)) =
      Pi.single (coreWiring S D (Function.update x t (Bool.xor (x t) c),sd)) 1 := by
  cases c <;> cases hx : x t <;>
    simp [Fintype.sum_bool, complexifyRealUnitary, RealToffoli.xReal, RealToffoli.xEntry, hx]

theorem edge_work_basis (g : TransducerCompiler.GateSynthesis.LowerGate (Fin 4))
    (x : CoreWire → Bool) (sd : S × D) :
    ((GraphWorkGate.edge g).eval S D).val *ᵥ Pi.single (coreWiring S D (x,sd)) 1 =
      ∑ y : Bool, (edgeTarget g).coefficient x y •
        (Pi.single (coreWiring S D (Function.update x (edgeTarget g).target y,sd)) 1 :
          Bool × (BranchSpace S D ⊕ BranchSpace S D) → ℂ) := by
  cases g with
  | x t =>
    have hh := TransducerCompiler.GateSynthesis.placeHom_basis
      (labelLowerWiring ((S × D) ⊕ (S × D)))
      (TransducerCompiler.GateSynthesis.LowerGate.eval (.x t))
      (x none,coreLabels x) (x none,Function.update (coreLabels x) t (!(coreLabels x t)))
      (coreInner x sd) (edge_x_basis t (x none) (coreLabels x))
    simp only [core_lower_input, core_label_update, coreLabels_read] at hh
    have hs := x_target_sum x sd (labelCore t) true
    simp only [ite_true,Bool.xor_true] at hs
    simpa only [edgeTarget,TargetGate.coefficient,TargetGate.coreEnabled,TargetGate.unitary,TargetGate.target,ite_true]
      using hh.trans hs.symm
  | cx c t hct =>
    have hh := TransducerCompiler.GateSynthesis.placeHom_basis
      (labelLowerWiring ((S × D) ⊕ (S × D)))
      (TransducerCompiler.GateSynthesis.LowerGate.eval (.cx c t hct))
      (x none,coreLabels x)
      (x none,Function.update (coreLabels x) t (Bool.xor (coreLabels x t) (coreLabels x c)))
      (coreInner x sd) (edge_cx_basis c t hct (x none) (coreLabels x))
    simp only [core_lower_input, core_label_update, coreLabels_read] at hh
    have hs := x_target_sum x sd (labelCore t) (x (labelCore c))
    simpa only [edgeTarget,TargetGate.coefficient,TargetGate.coreEnabled,TargetGate.unitary,
      TargetGate.target,decide_eq_true_eq] using hh.trans hs.symm
  | template c d t hcd hct hdt g =>
    cases g with
    | atom g =>
      cases g with
      | rotate θ =>
        have hh := placeHom_basis_expansion (labelLowerWiring ((S × D) ⊕ (S × D)))
          (TransducerCompiler.GateSynthesis.LowerGate.eval (.template c d t hcd hct hdt (.atom (.rotate θ))))
          (x none,coreLabels x) (coreInner x sd) (fun r => (r,coreLabels x))
          (fun r => (complexifyRealUnitary (RealToffoli.rotationReal θ)).val r (x none))
          (edge_rotate_basis c d t hcd hct hdt θ (x none) (coreLabels x))
        simpa only [GraphWorkGate.eval,core_lower_input,core_borrowed_update,edgeTarget,
          TargetGate.coefficient,TargetGate.coreEnabled,TargetGate.unitary,TargetGate.target,ite_true] using hh
      | controlA =>
        have hh := TransducerCompiler.GateSynthesis.placeHom_basis (labelLowerWiring ((S × D) ⊕ (S × D)))
          (TransducerCompiler.GateSynthesis.LowerGate.eval (.template c d t hcd hct hdt (.atom .controlA)))
          (x none,coreLabels x) (Bool.xor (x none) (coreLabels x c),coreLabels x)
          (coreInner x sd) (edge_controlA_basis c d t hcd hct hdt (x none) (coreLabels x))
        simp only [core_lower_input, core_borrowed_update,coreLabels_read] at hh
        have hs := x_target_sum x sd none (x (labelCore c))
        simpa only [edgeTarget,TargetGate.coefficient,TargetGate.coreEnabled,TargetGate.unitary,
          TargetGate.target,decide_eq_true_eq] using hh.trans hs.symm
      | controlB =>
        have hh := TransducerCompiler.GateSynthesis.placeHom_basis (labelLowerWiring ((S × D) ⊕ (S × D)))
          (TransducerCompiler.GateSynthesis.LowerGate.eval (.template c d t hcd hct hdt (.atom .controlB)))
          (x none,coreLabels x) (Bool.xor (x none) (coreLabels x d),coreLabels x)
          (coreInner x sd) (edge_controlB_basis c d t hcd hct hdt (x none) (coreLabels x))
        simp only [core_lower_input, core_borrowed_update,coreLabels_read] at hh
        have hs := x_target_sum x sd none (x (labelCore d))
        simpa only [edgeTarget,TargetGate.coefficient,TargetGate.coreEnabled,TargetGate.unitary,
          TargetGate.target,decide_eq_true_eq] using hh.trans hs.symm
    | copy =>
      have hh := TransducerCompiler.GateSynthesis.placeHom_basis (labelLowerWiring ((S × D) ⊕ (S × D)))
        (TransducerCompiler.GateSynthesis.LowerGate.eval (.template c d t hcd hct hdt .copy))
        (x none,coreLabels x) (x none,Function.update (coreLabels x) t (Bool.xor (coreLabels x t) (x none)))
        (coreInner x sd) (edge_copy_basis c d t hcd hct hdt (x none) (coreLabels x))
      simp only [core_lower_input, core_label_update,coreLabels_read] at hh
      have hs := x_target_sum x sd (labelCore t) (x none)
      simpa only [edgeTarget,TargetGate.coefficient,TargetGate.coreEnabled,TargetGate.unitary,
        TargetGate.target,decide_eq_true_eq] using hh.trans hs.symm

/-- Every graph work instruction changes a single named target, conditioned
on at most one existing bit, with exact coherent amplitudes. -/
theorem GraphWorkGate.target_basis (g : GraphWorkGate) (x : CoreWire → Bool) (sd : S × D) :
    (g.eval S D).val *ᵥ Pi.single (coreWiring S D (x,sd)) 1 =
      ∑ y : Bool, g.targetGate.coefficient x y •
        (Pi.single (coreWiring S D (Function.update x g.targetGate.target y,sd)) 1 :
          Bool × (BranchSpace S D ⊕ BranchSpace S D) → ℂ) := by
  cases g with
  | selectBit G =>
    rw [GraphWorkGate.eval,borrow_place]
    conv_lhs => rw [← core_select_input x sd]
    rw [placeHom_basis_sum]
    simp only [core_select_update,GraphWorkGate.targetGate,TargetGate.coefficient,
      TargetGate.coreEnabled,TargetGate.unitary,TargetGate.target,ite_true]
  | controlledHadamard =>
    have hh := core_controlled_basis (mixReal (-halfAmplitude) halfAmplitude_bound) x sd
    cases hc : x (some 0) <;>
      simpa [GraphWorkGate.eval,GraphWorkGate.targetGate,TargetGate.coefficient,
        TargetGate.coreEnabled,TargetGate.unitary,TargetGate.target,hc] using hh
  | controlledX =>
    have hh := core_controlled_basis RealToffoli.xReal x sd
    cases hc : x (some 0) <;>
      simpa [GraphWorkGate.eval,GraphWorkGate.targetGate,TargetGate.coefficient,
        TargetGate.coreEnabled,TargetGate.unitary,TargetGate.target,hc] using hh
  | edge g => exact edge_work_basis g x sd

end OptimalQLS.GraphEncoding
