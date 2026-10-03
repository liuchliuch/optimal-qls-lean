import OptimalQLS.Preparation.WorkGates.Placement

/-! # Preparation factor semantics on the literal source registers -/
noncomputable section
namespace OptimalQLS.Preparation.WorkGates
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
variable {D : Type*} [Fintype D] [DecidableEq D]

abbrev Source (a : ℕ) (D : Type*) := (Fin 8 × (Bits a × D)) × Bool
abbrev Physical (a : ℕ) (D : Type*) := GateSynthesis.Space (Wire (LogicalWire a)) × D

def sourceInsertion {a : ℕ} (dirty : Bool) : Source a D → Physical a D :=
  fun x => (cleanBasis dirty ((logicalEquiv a).symm ((x.1.1,x.1.2.1),x.2)),x.1.2.2)

/-- Complete wire-level register equivalence, with the three scratch coordinates
visible separately. No source sector is padded out or omitted. -/
def registerEquiv (a : ℕ) (D : Type*) : Source a D × (Bool × Bool × Bool) ≃ Physical a D where
  toFun p := ((p.2.1,Sum.elim
    ((logicalEquiv a).symm ((p.1.1.1,p.1.1.2.1),p.1.2))
    (fun i => if i=0 then p.2.2.1 else p.2.2.2)),p.1.1.2.2)
  invFun p :=
    let b := logicalEquiv a (fun i => p.1.2 (.inl i))
    (((b.1.1,(b.1.2,p.2)),b.2),(p.1.1,p.1.2 (.inr 0),p.1.2 (.inr 1)))
  left_inv p := by
    rcases p with ⟨⟨⟨j,s,d⟩,c⟩,z,f,r⟩
    simp
  right_inv p := by
    rcases p with ⟨⟨z,b⟩,d⟩
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext i
        cases i with
        | inl i => exact congrFun ((logicalEquiv a).symm_apply_apply (fun j => b (.inl j))) i
        | inr i => fin_cases i <;> rfl
    · rfl

theorem sourceInsertion_registerEquiv {a : ℕ} (dirty : Bool) (x : Source a D) :
    sourceInsertion dirty x=registerEquiv a D (x,(false,false,dirty)) := rfl

def sourceFactor {a : ℕ} {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    (external : Bool) (k : Fin 9) : Matrix (Source a D) (Source a D) ℂ :=
  Matrix.blockDiagonal (fun c : Bool => if !external || c then
    fiberMatrix (fun x : Bits a × D => labelOperation hμ hr (decide (x.1=fun _=>false)) k) else 1)

def physicalFactor {a : ℕ} {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    (external : Bool) (k : Fin 9) : Matrix.unitaryGroup (Physical a D) ℂ :=
  GateSynthesis.placeHom (Equiv.refl _) (phaseEval (workFactor (a := a) hμ hr external k))

/-- The clean injection retains all eight labels, including the three unused sectors. -/
theorem sourceInsertion_injective {a : ℕ} (dirty : Bool) :
    Function.Injective (sourceInsertion (D := D) (a := a) dirty) := by
  intro x y h
  change registerEquiv a D (x,(false,false,dirty))=registerEquiv a D (y,(false,false,dirty)) at h
  exact congrArg Prod.fst ((registerEquiv a D).injective h)

theorem sourceInsertion_isometry {a : ℕ} (dirty : Bool) :
    (basisInsertion (sourceInsertion (D := D) (a := a) dirty))ᴴ *
      basisInsertion (sourceInsertion (D := D) (a := a) dirty)=1 :=
  basisInsertion_isometry _ (sourceInsertion_injective dirty)

theorem sourceInsertion_scratch {a : ℕ} (dirty : Bool) (x : Source a D) :
    (sourceInsertion dirty x).1.1=false ∧
      (sourceInsertion dirty x).1.2 (.inr 0)=false ∧
      (sourceInsertion dirty x).1.2 (.inr 1)=dirty := by
  simp [sourceInsertion,cleanBasis,cleanBits]

def factorCoefficient {a : ℕ} {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    (external : Bool) (k : Fin 9) (j : Fin 8) (s : Bits a) (c y : Bool) : ℂ :=
  if ((!external || c) && labelControl k (decide (s=fun _=>false)) j) then
    (labelGate hμ hr k).val y (labelBits j (labelTarget k))
  else if y=labelBits j (labelTarget k) then 1 else 0

def replaceLabel (j : Fin 8) (k : Fin 9) (y : Bool) : Fin 8 :=
  labelEquiv.symm (Function.update (labelBits j) (labelTarget k) y)

theorem physicalFactor_basis {a : ℕ} {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    (external : Bool) (k : Fin 9) (dirty : Bool) (j : Fin 8) (s : Bits a) (d : D) (c : Bool) :
    (physicalFactor hμ hr external k).val *ᵥ Pi.single (sourceInsertion dirty ((j,(s,d)),c)) 1=
      ∑ y : Bool, factorCoefficient hμ hr external k j s c y •
        (Pi.single (sourceInsertion dirty ((replaceLabel j k y,(s,d)),c)) 1 : Physical a D→ℂ) := by
  have h := targetProgram_basis (controls (a := a) external k) (controls_injective external k)
    (pattern k) (target k) (controls_ne_target external k) (labelGate hμ hr k) dirty
    ((logicalEquiv a).symm ((j,s),c))
  simp only [targetCoefficient,controls_match,target,logicalEquiv_update] at h
  have hb : ((logicalEquiv a).symm ((j,s),c)) (.inl (labelTarget k))=
      labelBits j (labelTarget k) := rfl
  simp only [hb] at h
  exact blockDiagonal_basis_expansion
    (fun _ : D => (phaseEval (workFactor (a := a) hμ hr external k)).val) d
    (cleanBasis dirty ((logicalEquiv a).symm ((j,s),c)))
    (factorCoefficient hμ hr external k j s c)
    (fun y => cleanBasis dirty ((logicalEquiv a).symm ((replaceLabel j k y,s),c))) h

theorem fiberMatrix_one {F : Type*} [DecidableEq F] :
    fiberMatrix (fun _ : F => (1 : Matrix (Fin 8) (Fin 8) ℂ))=1 := by
  ext ⟨i,x⟩ ⟨j,y⟩
  simp [fiberMatrix,Matrix.one_apply,Prod.mk.injEq,and_comm,ite_and]

theorem sourceFactor_fiber {a : ℕ} {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    (external : Bool) (k : Fin 9) :
    sourceFactor (D := D) (a := a) hμ hr external k=
      Matrix.blockDiagonal (fun c : Bool => fiberMatrix (fun x : Bits a × D =>
        labelTargetMatrix (fun j => (!external || c) &&
          labelControl k (decide (x.1=fun _=>false)) j) (labelTarget k) (labelGate hμ hr k).val)) := by
  unfold sourceFactor
  congr 1
  funext c
  cases h : !external || c
  · simp [h,labelTargetMatrix_false,fiberMatrix_one]
  · simp [h,labelOperation]

theorem sourceFactor_basis {a : ℕ} {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    (external : Bool) (k : Fin 9) (j : Fin 8) (s : Bits a) (d : D) (c : Bool) :
    sourceFactor hμ hr external k *ᵥ Pi.single ((j,(s,d)),c) 1=
      ∑ y : Bool, factorCoefficient hμ hr external k j s c y •
        (Pi.single ((replaceLabel j k y,(s,d)),c) 1 : Source a D→ℂ) := by
  rw [sourceFactor_fiber]
  apply blockDiagonal_basis_expansion
  change Matrix.blockDiagonal (fun x : Bits a × D =>
    labelTargetMatrix (fun j => (!external || c) && labelControl k (decide (x.1=fun _=>false)) j)
      (labelTarget k) (labelGate hμ hr k).val) *ᵥ Pi.single (j,(s,d)) 1=_
  apply blockDiagonal_basis_expansion
  exact labelTargetMatrix_basis _ _ _ _

theorem physicalFactor_intertwines {a : ℕ} {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    (external : Bool) (k : Fin 9) (dirty : Bool) :
    (physicalFactor (D := D) (a := a) hμ hr external k).val*basisInsertion (sourceInsertion dirty)=
      basisInsertion (sourceInsertion dirty)*sourceFactor hμ hr external k := by
  apply basisInsertion_intertwines
  intro ⟨⟨j,s,d⟩,c⟩
  rw [physicalFactor_basis,sourceFactor_basis,Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul,basisInsertion_basis]

def physicalWork {a : ℕ} {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    (external : Bool) : Matrix.unitaryGroup (Physical a D) ℂ :=
  GateSynthesis.placeHom (Equiv.refl _) (phaseEval (workProgram a hμ hr external))

theorem physicalWork_product_intertwines {a : ℕ} {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    (external : Bool) (dirty : Bool) :
    (physicalWork (D := D) (a := a) hμ hr external).val*basisInsertion (sourceInsertion dirty)=
      basisInsertion (sourceInsertion dirty)*
        matrixEval (List.ofFn (fun k : Fin 9 => sourceFactor hμ hr external k)) := by
  have aux (l : List (Fin 9)) :
      (GateSynthesis.placeHom (Equiv.refl (Physical a D))
        (phaseEval ((l.map (workFactor (a := a) hμ hr external)).flatten))).val *
          basisInsertion (sourceInsertion dirty)=
      basisInsertion (sourceInsertion dirty)*matrixEval (l.map (sourceFactor hμ hr external)) := by
    induction l with
    | nil => simp [phaseEval,matrixEval]
    | cons k l ih =>
      simp only [List.map_cons,List.flatten_cons,phaseEval_append,map_mul,Submonoid.coe_mul,
        matrixEval]
      exact intertwines_mul _ _ _ _ _ (physicalFactor_intertwines hμ hr external k dirty) ih
  simpa only [physicalWork,workProgram,List.map_ofFn] using aux (List.ofFn (fun k : Fin 9=>k))

end OptimalQLS.Preparation.WorkGates
