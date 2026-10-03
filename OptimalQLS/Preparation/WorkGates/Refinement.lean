import OptimalQLS.Preparation.WorkGates.Macro

/-! # Exact clean-subspace refinement for mixed-polarity work macros -/
noncomputable section
namespace OptimalQLS.Preparation.WorkGates
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Two indexed scratch bits: the tested flag and the arbitrary borrowed bit. -/
abbrev Wire (I : Type*) := I ⊕ Fin 2

def controlWiring {n : ℕ} (c : Fin n → I) : SmallWire n → Wire I
  | .inl i => .inl (c i)
  | .inr i => .inr i

theorem controlWiring_injective {n : ℕ} (c : Fin n → I) (hc : Function.Injective c) :
    Function.Injective (controlWiring c) := by
  intro x y h
  cases x <;> cases y <;> simp_all [controlWiring,hc.eq_iff]

def patternWire (p : I → Bool) : Wire I → Bool := Sum.elim p (fun _ => false)

/-- All logical bits, including an external cache bit, are retained literally. -/
def cleanBits (dirty : Bool) (b : I → Bool) : Wire I → Bool :=
  Sum.elim b (fun i => if i=0 then false else dirty)

def cleanBasis (dirty : Bool) (b : I → Bool) : GateSynthesis.Space (Wire I) :=
  (false,cleanBits dirty b)

theorem cleanBits_injective (dirty : Bool) : Function.Injective (cleanBits (I := I) dirty) := by
  intro x y h
  funext i
  exact congrFun h (.inl i)

theorem cleanBasis_injective (dirty : Bool) : Function.Injective (cleanBasis (I := I) dirty) := by
  intro x y h
  exact cleanBits_injective dirty (congrArg Prod.snd h)

theorem cleanBits_update (dirty : Bool) (b : I → Bool) (t : I) (y : Bool) :
    Function.update (cleanBits dirty b) (.inl t) y=cleanBits dirty (Function.update b t y) := by
  funext i
  cases i <;> simp [cleanBits,Function.update_apply]

def targetCoefficient {n : ℕ} (c : Fin n → I) (p : I → Bool) (t : I)
    (U : Matrix Bool Bool ℂ) (b : I → Bool) (y : Bool) : ℂ :=
  if decide (∀ i : Fin n, b (c i)=p (c i)) then U y (b t) else if y=b t then 1 else 0

/-- Exact logical matrix of an ordinary controlled single-bit gate. -/
def targetMatrix {n : ℕ} (c : Fin n → I) (p : I → Bool) (t : I)
    (U : Matrix Bool Bool ℂ) : Matrix (I → Bool) (I → Bool) ℂ :=
  fun b d => ∑ y : Bool, targetCoefficient c p t U d y * (Pi.single (Function.update d t y) (1 : ℂ) : (I→Bool)→ℂ) b

theorem targetMatrix_basis {n : ℕ} (c : Fin n → I) (p : I → Bool) (t : I)
    (U : Matrix Bool Bool ℂ) (b : I → Bool) :
    targetMatrix c p t U *ᵥ Pi.single b 1 =
      ∑ y : Bool, targetCoefficient c p t U b y •
        (Pi.single (Function.update b t y) 1 : (I → Bool) → ℂ) := by
  ext d
  simp [targetMatrix,Matrix.mulVec_single_one]

def targetProgram {n : ℕ} (c : Fin n → I) (hc : Function.Injective c)
    (p : I → Bool) (t : I) (U : Matrix.unitaryGroup Bool ℂ) : List (PhaseGate (Wire I)) :=
  patternControlledTarget n (controlWiring c) (controlWiring_injective c hc) (.inl t)
    (by simp [controlWiring,smallTarget]) (patternWire p) U

theorem targetProgram_length {n : ℕ} (c : Fin n → I) (hc : Function.Injective c)
    (p : I → Bool) (t : I) (U : Matrix.unitaryGroup Bool ℂ) :
    (targetProgram c hc p t U).length ≤ 811*(n+1) :=
  patternControlledTarget_length _ _ _ _ _ _ _

theorem targetProgram_real {n : ℕ} (c : Fin n → I) (hc : Function.Injective c)
    (p : I → Bool) (t : I) (U : Matrix.unitaryGroup Bool ℂ)
    (hU : ∀ i j, (U.val i j).im=0) :
    ∀ g ∈ targetProgram c hc p t U, RealGate g :=
  patternControlledTarget_real _ _ _ _ _ _ _ hU

/-- Matrix equality includes arbitrary coherent inputs and arbitrary borrowed scratch.
Its sole scratch initialization is two clean bits, independent of the control count. -/
theorem targetProgram_intertwines {n : ℕ} (c : Fin n → I) (hc : Function.Injective c)
    (p : I → Bool) (t : I) (ht : ∀ i : Fin n, c i≠t)
    (U : Matrix.unitaryGroup Bool ℂ) (dirty : Bool) :
    (phaseEval (targetProgram c hc p t U)).val * basisInsertion (cleanBasis dirty)=
      basisInsertion (cleanBasis dirty) * targetMatrix c p t U.val := by
  apply basisInsertion_intertwines
  intro b
  rw [targetMatrix_basis,Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul,basisInsertion_basis]
  have h := patternControlledTarget_basis n (controlWiring c)
    (controlWiring_injective c hc) (.inl t) (by simp [controlWiring,smallTarget])
    (by intro i; simpa [controlWiring] using ht i) (patternWire p) U (cleanBits dirty b)
    (by simp [controlWiring,smallTarget,cleanBits])
  simp only [cleanBits_update] at h
  simpa only [targetProgram,cleanBasis,controlWiring,patternWire,
    cleanBits,Sum.elim_inl,targetCoefficient] using h

theorem targetProgram_basis {n : ℕ} (c : Fin n → I) (hc : Function.Injective c)
    (p : I → Bool) (t : I) (ht : ∀ i : Fin n, c i≠t)
    (U : Matrix.unitaryGroup Bool ℂ) (dirty : Bool) (b : I→Bool) :
    (phaseEval (targetProgram c hc p t U)).val *ᵥ Pi.single (cleanBasis dirty b) 1=
      ∑ y : Bool, targetCoefficient c p t U.val b y •
        (Pi.single (cleanBasis dirty (Function.update b t y)) 1 : GateSynthesis.Space (Wire I)→ℂ) := by
  have h := congrArg (fun M : Matrix (GateSynthesis.Space (Wire I)) (I→Bool) ℂ =>
    M*ᵥPi.single b 1) (targetProgram_intertwines c hc p t ht U dirty)
  simpa only [← Matrix.mulVec_mulVec,basisInsertion_basis,targetMatrix_basis,
    Matrix.mulVec_sum,Matrix.mulVec_smul] using h

/-- Arbitrary finite spectator data is unaffected by the literal gate placements. -/
theorem targetProgram_spectator {D : Type*} [Fintype D] [DecidableEq D]
    {n : ℕ} (c : Fin n → I) (hc : Function.Injective c)
    (p : I → Bool) (t : I) (ht : ∀ i : Fin n, c i≠t)
    (U : Matrix.unitaryGroup Bool ℂ) (dirty : Bool)
    (V : Matrix.unitaryGroup (I → Bool) ℂ) (hV : V.val=targetMatrix c p t U.val) :
    (GateSynthesis.placeHom (Equiv.refl (GateSynthesis.Space (Wire I) × D))
      (phaseEval (targetProgram c hc p t U))).val *
      basisInsertion (fun x : (I→Bool) × D => (cleanBasis dirty x.1,x.2))=
    basisInsertion (fun x : (I→Bool) × D => (cleanBasis dirty x.1,x.2)) *
      (GateSynthesis.placeHom (Equiv.refl ((I→Bool) × D)) V).val := by
  apply tensor_intertwines
  rw [hV]
  exact targetProgram_intertwines c hc p t ht U dirty

/-- Tensor naturality needs no unitarity assumption on the intermediate logical
matrices; it is an equality of their actual entries. -/
theorem tensorMatrix_intertwines {L P D : Type*} [Fintype L] [DecidableEq L]
    [Fintype P] [DecidableEq P] [Fintype D] [DecidableEq D]
    (f : L → P) (U : Matrix P P ℂ) (V : Matrix L L ℂ)
    (h : U*basisInsertion f=basisInsertion f*V) :
    (Matrix.blockDiagonal (fun _ : D => U)) *
        basisInsertion (fun x : L × D => (f x.1,x.2))=
      basisInsertion (fun x : L × D => (f x.1,x.2))*
        (Matrix.blockDiagonal (fun _ : D => V)) := by
  ext ⟨p,e⟩ ⟨x,d⟩
  have hh := congrFun (congrFun h p) x
  simp only [Matrix.mul_apply,basisInsertion] at hh
  by_cases hed : e=d
  · subst e
    simpa [Matrix.mul_apply,basisInsertion,Fintype.sum_prod_type,Matrix.blockDiagonal,ite_and] using hh
  · simp [Matrix.mul_apply,basisInsertion,Fintype.sum_prod_type,Matrix.blockDiagonal,ite_and,hed]

theorem blockDiagonal_basis_expansion {L D Y : Type*} [Fintype L] [DecidableEq L]
    [Fintype D] [DecidableEq D] [Fintype Y]
    (M : D → Matrix L L ℂ) (d : D) (i : L) (c : Y → ℂ) (j : Y → L)
    (h : M d *ᵥ Pi.single i 1=∑ y, c y • (Pi.single (j y) 1 : L→ℂ)) :
    Matrix.blockDiagonal M *ᵥ Pi.single (i,d) 1=
      ∑ y, c y • (Pi.single (j y,d) 1 : L×D→ℂ) := by
  ext ⟨p,e⟩
  have hh := congrFun h p
  simp only [Matrix.mulVec_single_one,Matrix.col_apply] at hh ⊢
  by_cases he : e=d
  · subst e
    simpa [Matrix.blockDiagonal,Pi.single_apply] using hh
  · simp [Matrix.blockDiagonal,Pi.single_apply,he]

/-- Execution-order matrix product, matching the elementary-gate evaluator. -/
def matrixEval {L : Type*} [Fintype L] [DecidableEq L] : List (Matrix L L ℂ) → Matrix L L ℂ
  | [] => 1
  | g::gs => matrixEval gs * g

theorem macroList_intertwines {K L P : Type*} [Fintype L] [DecidableEq L]
    [Fintype P] [DecidableEq P] (J : Matrix (GateSynthesis.Space P) L ℂ)
    (physical : K → List (PhaseGate P)) (logical : K → Matrix L L ℂ)
    (h : ∀ k, (phaseEval (physical k)).val*J=J*logical k) (l : List K) :
    (phaseEval ((l.map physical).flatten)).val*J=J*matrixEval (l.map logical) := by
  induction l with
  | nil => simp [phaseEval,matrixEval]
  | cons k l ih =>
    simp only [List.map_cons,List.flatten_cons,phaseEval_append,Submonoid.coe_mul,
      matrixEval]
    exact intertwines_mul J _ _ _ _ (h k) ih

end OptimalQLS.Preparation.WorkGates
