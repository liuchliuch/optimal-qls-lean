import OptimalQLS.Refinement.CostedExecution.LocalityCore

/-! # Actual one- and two-qubit tensors of the real synthesis leaves -/
noncomputable section
namespace OptimalQLS.Refinement.CostedExecution
open Matrix TransducerCompiler PolynomialTransform DirtyAncilla
open scoped Classical
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

/-- Coordinate order is synthesis, first control, second control, target. -/
def templateBits (x : RealToffoli.State) : Fin 4 → Bool :=
  ![x.1,x.2.1,x.2.2.1,x.2.2.2]

def rotateEmbedding : WireEmbedding boolCoordinates templateBits
    (Equiv.refl (Bool × RealToffoli.Sector)) where
  wire := ⟨fun _ => 0,fun i j _ => Subsingleton.elim i j⟩
  read := by intro x r i; cases i; rfl
  outside := by intro x y r j hj; fin_cases j <;> simp_all [templateBits]

def controlAFrame : (Bool × Bool) × (Bool × Bool) ≃ RealToffoli.State where
  toFun p := (p.1.1,p.1.2,p.2.1,p.2.2)
  invFun p := ((p.1,p.2.1),(p.2.2.1,p.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def controlBFrame : (Bool × Bool) × (Bool × Bool) ≃ RealToffoli.State where
  toFun p := (p.1.1,p.2.1,p.1.2,p.2.2)
  invFun p := ((p.1,p.2.2.1),(p.2.1,p.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def copyFrame : (Bool × Bool) × (Bool × Bool) ≃ RealToffoli.State where
  toFun p := (p.1.1,p.2.1,p.2.2,p.1.2)
  invFun p := ((p.1,p.2.2.2),(p.2.1,p.2.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

def controlAEmbedding : WireEmbedding pairCoordinates templateBits controlAFrame where
  wire := ⟨fun i=>Fin.castLE (by decide : 2≤4) i,by intro i j h; exact Fin.ext (congrArg (fun k : Fin 4=>k.val) h)⟩
  read := by intro x r i; fin_cases i <;> rfl
  outside := by intro x y r j hj; fin_cases j <;> simp_all [controlAFrame,templateBits]

def controlBEmbedding : WireEmbedding pairCoordinates templateBits controlBFrame where
  wire := ⟨fun i=>if i=0 then 0 else 2,by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩
  read := by intro x r i; fin_cases i <;> rfl
  outside := by
    intro x y r j hj
    fin_cases j <;> simp_all [controlBFrame,templateBits]

def copyEmbedding : WireEmbedding pairCoordinates templateBits copyFrame where
  wire := ⟨fun i=>if i=0 then 0 else 3,by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩
  read := by intro x r i; fin_cases i <;> rfl
  outside := by intro x y r j hj; fin_cases j <;> simp_all [copyFrame,templateBits]

def copySmallEquiv : Equiv.Perm (Bool × Bool) where
  toFun p := (p.1,Bool.xor p.2 p.1)
  invFun p := (p.1,Bool.xor p.2 p.1)
  left_inv p := by rcases p with ⟨a,b⟩; cases a <;> cases b <;> rfl
  right_inv p := by rcases p with ⟨a,b⟩; cases a <;> cases b <;> rfl

theorem template_controlA_tensor : RealToffoli.ComputeGate.controlA.eval =
    GateSynthesis.placeHom controlAFrame
      (controlledOn id (RealToffoli.complexifyHom RealToffoli.xReal)) := by
  apply Subtype.ext
  ext ⟨z,a,b,y⟩ ⟨z',a',b',y'⟩
  change _ = (if (b,y)=(b',y') then _ else 0)
  simp only [RealToffoli.ComputeGate.eval,RealToffoli.block,RealToffoli.ComputeGate.small,
    Matrix.blockDiagonal_apply,controlledOn,controlAFrame]
  by_cases ha : a=a' <;> by_cases hb : b=b' <;> by_cases hy : y=y' <;>
    simp [ha,hb,hy,RealToffoli.controlledX,apply_ite,map_one,Matrix.blockDiagonal_apply]

theorem template_controlB_tensor : RealToffoli.ComputeGate.controlB.eval =
    GateSynthesis.placeHom controlBFrame
      (controlledOn id (RealToffoli.complexifyHom RealToffoli.xReal)) := by
  apply Subtype.ext
  ext ⟨z,a,b,y⟩ ⟨z',a',b',y'⟩
  change _ = (if (a,y)=(a',y') then _ else 0)
  simp only [RealToffoli.ComputeGate.eval,RealToffoli.block,RealToffoli.ComputeGate.small,
    Matrix.blockDiagonal_apply,controlledOn,controlBFrame]
  by_cases ha : a=a' <;> by_cases hb : b=b' <;> by_cases hy : y=y' <;>
    simp [ha,hb,hy,RealToffoli.controlledX,apply_ite,map_one,Matrix.blockDiagonal_apply]

theorem template_copy_tensor : RealToffoli.copyUnitary =
    GateSynthesis.placeHom copyFrame (permutation copySmallEquiv) := by
  apply Subtype.ext
  ext ⟨z,a,b,y⟩ ⟨z',a',b',y'⟩
  change _ = (if (a,b)=(a',b') then _ else 0)
  simp only [RealToffoli.copyUnitary,permutation,
    RealToffoli.copyEquiv,copySmallEquiv]
  by_cases hz : z=z' <;> by_cases ha : a=a' <;> by_cases hb : b=b' <;>
    by_cases hy : Bool.xor y z=y' <;> simp [hz,ha,hb,hy,copyFrame]

theorem template_leaf_local (g : RealToffoli.Gate) : IsTwoLocal templateBits g.eval := by
  cases g with
  | atom g => cases g with
    | rotate θ =>
      exact .tensor (by simp) boolCoordinates (Equiv.refl _) rotateEmbedding
        (RealToffoli.complexifyHom (RealToffoli.rotationReal θ))
    | controlA =>
      rw [RealToffoli.Gate.eval,template_controlA_tensor]
      exact .tensor (by simp) pairCoordinates controlAFrame controlAEmbedding _
    | controlB =>
      rw [RealToffoli.Gate.eval,template_controlB_tensor]
      exact .tensor (by simp) pairCoordinates controlBFrame controlBEmbedding _
  | copy =>
    rw [RealToffoli.Gate.eval,template_copy_tensor]
    exact .tensor (by simp) pairCoordinates copyFrame copyEmbedding _

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def templateWiring_embedding (c d t : ι) (hcd : c ≠ d) (hct : c ≠ t) (hdt : d ≠ t) :
    WireEmbedding templateBits phaseBits (GateSynthesis.templateWiring c d t hcd hct hdt) where
  wire := ⟨fun i=>if i=0 then .inl () else if i=1 then .inr c else if i=2 then .inr d else .inr t,by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all⟩
  read := by
    intro x r i
    fin_cases i <;> simp [GateSynthesis.templateWiring,GateSynthesis.splitTriple,
      phaseBits,templateBits,hcd,hct,hdt,Ne.symm hcd,Ne.symm hct,Ne.symm hdt]
  outside := by
    intro x y r j hj
    cases j with
    | inl j => exact False.elim (hj 0 (by cases j; rfl))
    | inr j =>
      have hc : j ≠ c := by intro h; exact hj 1 (by simp [h])
      have hd : j ≠ d := by intro h; exact hj 2 (by simp [h])
      have ht : j ≠ t := by intro h; exact hj 3 (by simp [h])
      simp [GateSynthesis.templateWiring,GateSynthesis.splitTriple,phaseBits,hc,hd,ht]

/-- The template is local on arbitrary synthesis-bit states, not just its clean input. -/
theorem lower_template_local (c d t : ι) (hcd : c ≠ d) (hct : c ≠ t) (hdt : d ≠ t)
    (g : RealToffoli.Gate) :
    IsTwoLocal phaseBits (GateSynthesis.LowerGate.eval (.template c d t hcd hct hdt g)) :=
  IsTwoLocal.place _ (templateWiring_embedding c d t hcd hct hdt) _ (template_leaf_local g)


def boolNotEquiv : Equiv.Perm Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv b := by cases b <;> rfl
  right_inv b := by cases b <;> rfl

theorem permutation_basis_exact {A : Type} [Fintype A] [DecidableEq A]
    (e : Equiv.Perm A) (x : A) :
    (permutation e).val *ᵥ Pi.single x 1 = Pi.single (e.symm x) 1 := by
  rw [permutation_apply]
  ext y
  simp [Pi.single_apply,Equiv.apply_eq_iff_eq_symm_apply]

/-- A lower X is one tensor factor on arbitrary values of the synthesis bit. -/
theorem lower_x_tensor (t : ι) : GateSynthesis.LowerGate.eval (.x t) =
    GateSynthesis.placeHom (singleWiring t) (permutation boolNotEquiv) := by
  apply Subtype.ext
  apply Matrix.ext_of_mulVec_single
  intro p
  rcases p with ⟨z,b⟩
  have hl := GateSynthesis.placeHom_basis (Equiv.prodComm (ι → Bool) Bool)
    (BinaryClock.programUnitary [BinaryClock.Gate.x t]) b
    ((BinaryClock.Gate.x t).act b) z (by
      simpa only [BinaryClock.run_cons,BinaryClock.run_nil] using
        BinaryClock.programUnitary_basis [BinaryClock.Gate.x t] b)
  have hr := GateSynthesis.placeHom_basis (singleWiring t) (permutation boolNotEquiv)
    (b t) (!(b t)) (z,fun i=>b i.val) (permutation_basis_exact boolNotEquiv (b t))
  have hi : singleWiring t (b t,(z,fun i=>b i.val)) = (z,b) :=
    (singleWiring t).apply_symm_apply (z,b)
  have ho : singleWiring t (!(b t),(z,fun i=>b i.val)) =
      (z,(BinaryClock.Gate.x t).act b) := by
    apply Prod.ext
    · rfl
    · funext i
      simp [singleWiring,BinaryClock.Gate.act,Function.update_apply]
  rw [hi,ho] at hr
  exact hl.trans hr.symm

/-- A lower CNOT is an exact two-bit tensor, without a clean-input hypothesis. -/
theorem lower_cx_tensor (c t : ι) (hct : c ≠ t) :
    GateSynthesis.LowerGate.eval (.cx c t hct) =
      GateSynthesis.placeHom (pairWiring c t hct) (permutation copySmallEquiv) := by
  apply Subtype.ext
  apply Matrix.ext_of_mulVec_single
  intro p
  rcases p with ⟨z,b⟩
  have hl := GateSynthesis.placeHom_basis (Equiv.prodComm (ι → Bool) Bool)
    (BinaryClock.programUnitary [BinaryClock.Gate.cx c t hct]) b
    ((BinaryClock.Gate.cx c t hct).act b) z (by
      simpa only [BinaryClock.run_cons,BinaryClock.run_nil] using
        BinaryClock.programUnitary_basis [BinaryClock.Gate.cx c t hct] b)
  have hr := GateSynthesis.placeHom_basis (pairWiring c t hct) (permutation copySmallEquiv)
    (b c,b t) (b c,Bool.xor (b t) (b c)) (z,fun i=>b i.val)
    (permutation_basis_exact copySmallEquiv (b c,b t))
  have hi : pairWiring c t hct ((b c,b t),(z,fun i=>b i.val)) = (z,b) :=
    (pairWiring c t hct).apply_symm_apply (z,b)
  have ho : pairWiring c t hct ((b c,Bool.xor (b t) (b c)),(z,fun i=>b i.val)) =
      (z,(BinaryClock.Gate.cx c t hct).act b) := by
    apply Prod.ext
    · rfl
    · funext i
      by_cases hc : i=c
      · subst i; simp [pairWiring,BinaryClock.Gate.act,Function.update_apply,hct]
      · by_cases ht : i=t <;> simp [pairWiring,BinaryClock.Gate.act,Function.update_apply,hc,ht,hct,Ne.symm hct]
  rw [hi,ho] at hr
  exact hl.trans hr.symm

theorem lower_leaf_local (g : GateSynthesis.LowerGate ι) : IsTwoLocal phaseBits g.eval := by
  cases g with
  | x t =>
    rw [lower_x_tensor]
    exact .tensor (by simp) boolCoordinates (singleWiring t) (singleWiring_embedding t) _
  | cx c t hct =>
    rw [lower_cx_tensor]
    exact .tensor (by simp) pairCoordinates (pairWiring c t hct) (pairWiring_embedding c t hct) _
  | template c d t hcd hct hdt g => exact lower_template_local c d t hcd hct hdt g

/-- Every source phase leaf is a genuine one/two-qubit tensor on its literal
named wires, including the reusable synthesis bit when the template touches it. -/
theorem phase_leaf_local (g : PhaseGate ι) : IsTwoLocal phaseBits g.eval := by
  cases g with
  | real g => exact lower_leaf_local g
  | phase t φ =>
    exact .tensor (by simp) boolCoordinates (singleWiring t) (singleWiring_embedding t) _
  | pairPhase c t hct φ =>
    exact .tensor (by simp) pairCoordinates (pairWiring c t hct) (pairWiring_embedding c t hct) _
  | single t U => exact phase_single_local t U
  | pair c t hct U => exact phase_pair_local c t hct U

end OptimalQLS.Refinement.CostedExecution
