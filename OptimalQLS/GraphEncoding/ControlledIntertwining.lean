import OptimalQLS.GraphEncoding.WorkBasis
import OptimalQLS.PolynomialTransform.GraphAttachmentWiring

/-! # Exact clean-scratch realization of masked graph work gates -/
noncomputable section
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 1000000
namespace OptimalQLS.GraphEncoding
open Matrix PolynomialTransform TransducerCompiler DirtyAncilla
variable {S D W V : Type*} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]
  [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]

def controlledAssignment (m : Bool × Bool) (x : CoreWire → Bool) : ControlledGraphWire → Bool
  | .inl (.inl i) => ![m.1,m.2] i
  | .inl (.inr i) => x i
  | .inr _ => false

def corePhysicalWiring (S D : Type*) : ((CoreWire → Bool) × (S × D)) ≃
    PhysicalSignal S × (Fin 4 × D) :=
  (coreWiring S D).trans (realizedPhysicalWiring S D)

theorem graphLocalClean_core (m : Bool × Bool) (x : CoreWire → Bool) (sd : S × D) :
    graphLocalClean (m,corePhysicalWiring S D (x,sd)) = ((false,controlledAssignment m x),sd) := by
  cases hs : x (some 0) <;> cases hd : x (some 4) <;>
    simp [graphLocalClean,graphLocalWiring,corePhysicalWiring,coreWiring,
      realizedPhysicalWiring,physicalWiring,labelDistribution,labelWiring,coreLabels,coreInner,hs,hd]
  all_goals
    congr 1
    funext i
    rcases i with ((i|(_|i))|i)
    · fin_cases i <;> simp [controlledAssignment]
    · rfl
    · fin_cases i <;> simp [controlledAssignment,hs,hd]
    · simp [controlledAssignment]

theorem controlledAssignment_update (m : Bool × Bool) (x : CoreWire → Bool) (t : CoreWire) (y : Bool) :
    Function.update (controlledAssignment m x) (coreWire t) y =
      controlledAssignment m (Function.update x t y) := by
  ext i
  rcases i with ((i|i)|i) <;> simp [controlledAssignment,coreWire,Function.update_apply]

theorem localTargetCode_basis (mask m : Bool × Bool) (g : TargetGate)
    (x : CoreWire → Bool) (sd : S × D) :
    (elementaryPlacement (D := S × D) (phaseEval (g.code mask))).val *ᵥ
      Pi.single ((false,controlledAssignment m x),sd) 1 =
      ∑ y : Bool, (if m=mask then g.coefficient x y else if y=x g.target then 1 else 0) •
        (Pi.single ((false,controlledAssignment m (Function.update x g.target y)),sd) 1 :
          ElementarySpace ControlledGraphWire (S × D) → ℂ) := by
  classical
  have hh := placeHom_basis_expansion (Equiv.refl _)
    (phaseEval (g.code mask)) (false,controlledAssignment m x) sd
    (fun y => (false,Function.update (controlledAssignment m x) (coreWire g.target) y))
    (fun y => if controlledAssignment m x (maskWire 0)=mask.1 ∧
        controlledAssignment m x (maskWire 1)=mask.2 ∧ g.test (controlledAssignment m x)
      then (complexifyRealUnitary g.unitary).val y (controlledAssignment m x (coreWire g.target))
      else if y=controlledAssignment m x (coreWire g.target) then 1 else 0)
    (g.code_basis mask (controlledAssignment m x) rfl)
  dsimp only [Equiv.refl_apply] at hh
  change (TransducerCompiler.GateSynthesis.placeHom (Equiv.refl _) (phaseEval (g.code mask))).val *ᵥ _ = _
  rw [hh]
  apply Finset.sum_congr rfl
  intro y _
  rw [controlledAssignment_update]
  congr 1
  by_cases hm : m=mask
  · subst m
    cases g <;> simp [controlledAssignment,maskWire,coreWire,TargetGate.test,
      TargetGate.coefficient,TargetGate.coreEnabled,TargetGate.target,TargetGate.unitary]
  · have hn : ¬(m.1=mask.1 ∧ m.2=mask.2) := fun h => hm (Prod.ext h.1 h.2)
    simp [controlledAssignment,maskWire,coreWire,hm,hn,← and_assoc]

theorem rewire_basis_expansion {Y : Type*} [Fintype Y]
    (e : W ≃ V) (U : Matrix.unitaryGroup W ℂ) (i : W)
    (out : Y → W) (coef : Y → ℂ)
    (h : U.val *ᵥ Pi.single i 1 = ∑ y, coef y • (Pi.single (out y) 1 : W → ℂ)) :
    (rewireUnitary e U).val *ᵥ Pi.single (e i) 1 =
      ∑ y, coef y • (Pi.single (e (out y)) 1 : V → ℂ) := by
  rw [rewire_apply]
  have he : (Pi.single (e i) (1:ℂ) : V → ℂ) ∘ e = Pi.single i 1 := by
    ext k; simp [Pi.single_apply,e.injective.eq_iff]
  rw [he,h]
  ext k
  simp [Pi.single_apply,Equiv.symm_apply_eq]

theorem maskedGraphPort_insertion (mask m : Bool × Bool) (U : Matrix.unitaryGroup W ℂ) :
    ((maskedGraphPort W mask).apply U).val * basisInsertion (fun w : W => (m,w)) =
      basisInsertion (fun w : W => (m,w)) * (if m=mask then U.val else 1) := by
  ext ⟨c,i⟩ j
  by_cases hc : c=m
  · subst c
    simp [Matrix.mul_apply,basisInsertion,maskedGraphPort_apply_entries]
    split_ifs <;> simp_all [Matrix.one_apply]
  · simp [Matrix.mul_apply,basisInsertion,maskedGraphPort_apply_entries,hc]

theorem maskedGraphPort_basis_expansion {Y : Type*} [Fintype Y]
    (mask m : Bool × Bool) (U : Matrix.unitaryGroup W ℂ) (i : W)
    (out : Y → W) (coef : Y → ℂ)
    (h : U.val *ᵥ Pi.single i 1 = ∑ y, coef y • (Pi.single (out y) 1 : W → ℂ)) :
    ((maskedGraphPort W mask).apply U).val *ᵥ Pi.single (m,i) 1 =
      if m=mask then ∑ y, coef y • (Pi.single (m,out y) 1 : (Bool × Bool) × W → ℂ)
      else Pi.single (m,i) 1 := by
  rw [← basisInsertion_basis (fun w : W => (m,w)),Matrix.mulVec_mulVec,
    maskedGraphPort_insertion,← Matrix.mulVec_mulVec]
  by_cases hm : m=mask
  · simp only [hm,ite_true,h,Matrix.mulVec_sum,Matrix.mulVec_smul,basisInsertion_basis]
  · simp only [hm,ite_false,Matrix.one_mulVec,basisInsertion_basis]

/-- The full matrix intertwining theorem, including original-register spectators
and exact restoration of the same three scratch bits used by QSVT. -/
theorem GraphWorkGate.controlledCode_intertwines (mask : Bool × Bool) (g : GraphWorkGate) :
    (elementaryPlacement (D := S × D) (phaseEval (g.controlledCode mask))).val *
      basisInsertion (graphLocalClean (S := S) (D := D)) =
    basisInsertion (graphLocalClean (S := S) (D := D)) *
      ((maskedGraphPort (PhysicalSignal S × (Fin 4 × D)) mask).apply
        (rewireUnitary (realizedPhysicalWiring S D) (g.eval S D))).val := by
  apply basisInsertion_intertwines
  intro j
  rcases j with ⟨m,j⟩
  obtain ⟨⟨x,sd⟩,rfl⟩ := (corePhysicalWiring S D).surjective j
  rw [graphLocalClean_core]
  have hbase := rewire_basis_expansion (realizedPhysicalWiring S D) (g.eval S D)
    (coreWiring S D (x,sd))
    (fun y => coreWiring S D (Function.update x g.targetGate.target y,sd))
    (g.targetGate.coefficient x) (g.target_basis x sd)
  have hm := maskedGraphPort_basis_expansion mask m
    (rewireUnitary (realizedPhysicalWiring S D) (g.eval S D))
    (corePhysicalWiring S D (x,sd))
    (fun y => corePhysicalWiring S D (Function.update x g.targetGate.target y,sd))
    (g.targetGate.coefficient x) hbase
  rw [hm]
  change (elementaryPlacement (D := S × D) (phaseEval (g.targetGate.code mask))).val *ᵥ _ = _
  rw [localTargetCode_basis]
  by_cases hmask : m=mask
  · simp only [hmask,ite_true,Matrix.mulVec_sum,Matrix.mulVec_smul,basisInsertion_basis,
      graphLocalClean_core]
  · simp only [hmask,ite_false,basisInsertion_basis,graphLocalClean_core]
    have hu : Function.update x g.targetGate.target (x g.targetGate.target) = x :=
      Function.update_eq_self _ _
    rw [Finset.sum_eq_single (x g.targetGate.target)]
    · simp [hu]
    · intro y _ hy; simp [hy]
    · simp

end OptimalQLS.GraphEncoding
