import OptimalQLS.Preparation.CompilerPermutation

/-! # Physical P/work/P-inverse attachment for the actual compiler label frame -/
noncomputable section
namespace OptimalQLS.Preparation.CompilerAttachment
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
open WorkGates
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
variable {D : Type*} [Fintype D] [DecidableEq D]

abbrev WorkSource (a : ℕ) (D : Type*) := Base (Bool × (Bits a × D)) × Bool

def targetWorkWiring (a : ℕ) (D : Type*) : WorkSource a D ≃ WorkGates.Source a D :=
  Equiv.prodCongr (compilerWiring (Bits a × D)) (Equiv.refl Bool)

def rawLabelEquiv : Fin 8 ≃ Fin 8 :=
  compilerLabel.symm.trans (compilerBitEquiv.trans WorkGates.labelEquiv.symm)

def rawWorkWiring (a : ℕ) (D : Type*) : WorkSource a D ≃ WorkGates.Source a D :=
  (targetWorkWiring a D).trans
    (Equiv.prodCongr (Equiv.prodCongr rawLabelEquiv (Equiv.refl (Bits a × D))) (Equiv.refl Bool))

def workInsertion {a : ℕ} (dirty : Bool) : WorkSource a D → WorkGates.Physical a D :=
  WorkGates.sourceInsertion dirty ∘ rawWorkWiring a D

def workRegisterEquiv (a : ℕ) (D : Type*) :
    WorkSource a D × (Bool × Bool × Bool) ≃ WorkGates.Physical a D :=
  (Equiv.prodCongr (rawWorkWiring a D) (Equiv.refl (Bool × Bool × Bool))).trans
    (WorkGates.registerEquiv a D)

theorem workInsertion_registerEquiv {a : ℕ} (dirty : Bool) (x : WorkSource a D) :
    workInsertion dirty x=workRegisterEquiv a D (x,(false,false,dirty)) := rfl

def rawLogical {a : ℕ} (b : Bool) (l : Label) (s : Bits a) (c : Bool) : WorkGates.LogicalBits a :=
  Sum.elim (compilerBitEquiv (b,l)) (Sum.elim s (fun _=>c))

def targetLogical {a : ℕ} (b : Bool) (l : Label) (s : Bits a) (c : Bool) : WorkGates.LogicalBits a :=
  Sum.elim (WorkGates.labelEquiv (compilerLabel (b,l))) (Sum.elim s (fun _=>c))

theorem workInsertion_apply {a : ℕ} (dirty b : Bool) (l : Label) (s : Bits a) (c : Bool) (d : D) :
    workInsertion dirty (((b,(s,d)),l),c)=(WorkGates.cleanBasis dirty (rawLogical b l s c),d) := by
  cases b <;> cases l <;> rfl

theorem targetInsertion_apply {a : ℕ} (dirty b : Bool) (l : Label) (s : Bits a) (c : Bool) (d : D) :
    WorkGates.sourceInsertion dirty (targetWorkWiring a D (((b,(s,d)),l),c))=
      (WorkGates.cleanBasis dirty (targetLogical b l s c),d) := rfl

def permutationWire (a : ℕ) : Fin 3 → WorkGates.Wire (WorkGates.LogicalWire a) :=
  fun i => .inl (.inl i)

theorem permutationWire_injective (a : ℕ) : Function.Injective (permutationWire a) := by
  intro i j h
  simpa [permutationWire] using h

def mappedPermutation (a : ℕ) : Program (WorkGates.Wire (WorkGates.LogicalWire a)) :=
  mapProgram (permutationWire a) (permutationWire_injective a) compilerPermutation

theorem mappedPermutation_run {a : ℕ} (dirty b : Bool) (l : Label) (s : Bits a) (c : Bool) :
    run (mappedPermutation a) (WorkGates.cleanBits dirty (rawLogical b l s c))=
      WorkGates.cleanBits dirty (targetLogical b l s c) := by
  ext w
  cases w with
  | inr i =>
    exact mapProgram_outside (permutationWire a) (permutationWire_injective a)
      compilerPermutation (WorkGates.cleanBits dirty (rawLogical b l s c))
      (Sum.inr i) (by simp [permutationWire])
  | inl w => cases w with
    | inr i =>
      exact mapProgram_outside (permutationWire a) (permutationWire_injective a)
        compilerPermutation (WorkGates.cleanBits dirty (rawLogical b l s c))
        (Sum.inl (Sum.inr i)) (by simp [permutationWire])
    | inl i =>
      have h := congrFun (mapProgram_pullback (permutationWire a) (permutationWire_injective a)
        compilerPermutation (WorkGates.cleanBits dirty (rawLogical b l s c))) i
      have he : WorkGates.cleanBits dirty (rawLogical b l s c) ∘ permutationWire a=compilerBitEquiv (b,l) := rfl
      rw [he,compilerPermutation_run] at h
      exact h

def forwardWorkPermutation (a : ℕ) : List (PhaseGate (WorkGates.Wire (WorkGates.LogicalWire a))) :=
  (GateSynthesis.lowerProgram (mappedPermutation a)).map PhaseGate.real

def reverseWorkPermutation (a : ℕ) : List (PhaseGate (WorkGates.Wire (WorkGates.LogicalWire a))) :=
  (GateSynthesis.lowerProgram (mappedPermutation a).reverse).map PhaseGate.real

def placedPhaseWord {a : ℕ} (code : List (PhaseGate (WorkGates.Wire (WorkGates.LogicalWire a)))) :
    Matrix.unitaryGroup (WorkGates.Physical a D) ℂ := GateSynthesis.placeHom (Equiv.refl _) (phaseEval code)

theorem forwardWorkPermutation_basis {a : ℕ} (dirty : Bool) (x : WorkSource a D) :
    (placedPhaseWord (forwardWorkPermutation a)).val*ᵥPi.single (workInsertion dirty x) 1=
      Pi.single (WorkGates.sourceInsertion dirty (targetWorkWiring a D x)) 1 := by
  rcases x with ⟨⟨⟨b,s,d⟩,l⟩,c⟩
  rw [workInsertion_apply,targetInsertion_apply]
  change (GateSynthesis.placeHom (Equiv.refl _) (phaseEval (forwardWorkPermutation a))).val*ᵥ_= _
  rw [forwardWorkPermutation,phaseEval_real]
  apply GateSynthesis.placeHom_basis (Equiv.refl _)
  dsimp only [WorkGates.cleanBasis]
  rw [GateSynthesis.lowerProgram_basis,mappedPermutation_run]

theorem reverseWorkPermutation_basis {a : ℕ} (dirty : Bool) (x : WorkSource a D) :
    (placedPhaseWord (reverseWorkPermutation a)).val*ᵥ
      Pi.single (WorkGates.sourceInsertion dirty (targetWorkWiring a D x)) 1=
      Pi.single (workInsertion dirty x) 1 := by
  rcases x with ⟨⟨⟨b,s,d⟩,l⟩,c⟩
  rw [workInsertion_apply,targetInsertion_apply]
  change (GateSynthesis.placeHom (Equiv.refl _) (phaseEval (reverseWorkPermutation a))).val*ᵥ_= _
  rw [reverseWorkPermutation,phaseEval_real]
  apply GateSynthesis.placeHom_basis (Equiv.refl _)
  dsimp only [WorkGates.cleanBasis]
  rw [GateSynthesis.lowerProgram_basis,← mappedPermutation_run dirty b l s c,run_reverse_run]

theorem insertion_comp {L M P : Type*} [Fintype L] [DecidableEq L]
    [Fintype M] [DecidableEq M] [Fintype P] [DecidableEq P] (f : M → P) (g : L → M) :
    basisInsertion f*basisInsertion g=basisInsertion (f ∘ g) := by
  ext i j
  simp [basisInsertion,Matrix.mul_apply]

theorem insertion_equiv_natural {L M : Type*} [Fintype L] [DecidableEq L]
    [Fintype M] [DecidableEq M] (e : L ≃ M) (U : Matrix.unitaryGroup M ℂ) :
    U.val*basisInsertion e=basisInsertion e*(rewireUnitary e.symm U).val := by
  ext i j
  have hei (k : L) : i=e k ↔ k=e.symm i := by
    constructor
    · intro h; simpa using (congrArg e.symm h).symm
    · intro h; rw [h,e.apply_symm_apply]
  simp [basisInsertion,Matrix.mul_apply,rewireUnitary,hei]

def compilerSourceWork {a : ℕ} {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) (external : Bool) :
    Matrix.unitaryGroup (WorkSource a D) ℂ :=
  rewireUnitary (targetWorkWiring a D).symm (WorkGates.sourceWork hμ hr external)

theorem compilerSourceWork_eq {a : ℕ} {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) (external : Bool) :
    compilerSourceWork (D := D) (a := a) hμ hr external=
      controlledOn (fun c : Bool=>!external||c)
        (compilerWork (signalProjector (D := D) (fun _ : Fin a=>false))
          (signalProjector_star _) (signalProjector_idempotent _) hμ hr) := by
  apply Subtype.ext
  ext ⟨i,c⟩ ⟨j,d⟩
  by_cases h : c=d <;> cases external <;> cases c <;>
    simp_all [compilerSourceWork,targetWorkWiring,WorkGates.sourceWork,compilerWork,
      rewireUnitary,controlledOn,Matrix.blockDiagonal_apply,Matrix.one_apply,
      (compilerWiring (Bits a × D)).injective.eq_iff]

def compiledWorkProgram (a : ℕ) {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) (external : Bool) :
    List (PhaseGate (WorkGates.Wire (WorkGates.LogicalWire a))) :=
  forwardWorkPermutation a ++ WorkGates.workProgram a hμ hr external ++ reverseWorkPermutation a

theorem compiledWorkProgram_intertwines {a : ℕ} {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    (external dirty : Bool) :
    (placedPhaseWord (D := D) (compiledWorkProgram a hμ hr external)).val*basisInsertion (workInsertion dirty)=
      basisInsertion (workInsertion dirty)*(compilerSourceWork hμ hr external).val := by
  have hf : (placedPhaseWord (D := D) (forwardWorkPermutation a)).val*basisInsertion (workInsertion dirty)=
      basisInsertion (WorkGates.sourceInsertion dirty ∘ targetWorkWiring a D) := by
    apply Matrix.ext_of_mulVec_single
    intro x
    rw [← Matrix.mulVec_mulVec,basisInsertion_basis,basisInsertion_basis]
    exact forwardWorkPermutation_basis dirty x
  have hr' : (placedPhaseWord (D := D) (reverseWorkPermutation a)).val*
      basisInsertion (WorkGates.sourceInsertion dirty ∘ targetWorkWiring a D)=basisInsertion (workInsertion dirty) := by
    apply Matrix.ext_of_mulVec_single
    intro x
    rw [← Matrix.mulVec_mulVec,basisInsertion_basis,basisInsertion_basis]
    exact reverseWorkPermutation_basis dirty x
  have hw : (placedPhaseWord (D := D) (WorkGates.workProgram a hμ hr external)).val*
      basisInsertion (WorkGates.sourceInsertion dirty ∘ targetWorkWiring a D)=
      basisInsertion (WorkGates.sourceInsertion dirty ∘ targetWorkWiring a D)*(compilerSourceWork hμ hr external).val := by
    change (WorkGates.physicalWork hμ hr external).val*_
      =_*(compilerSourceWork hμ hr external).val
    rw [← insertion_comp,← Matrix.mul_assoc,WorkGates.workProgram_intertwines,
      Matrix.mul_assoc,insertion_equiv_natural,← Matrix.mul_assoc,insertion_comp]
    rfl
  simp only [compiledWorkProgram,placedPhaseWord,phaseEval_append,map_mul,Submonoid.coe_mul]
  simp only [placedPhaseWord] at hf hr' hw
  rw [Matrix.mul_assoc,Matrix.mul_assoc,hf,hw,← Matrix.mul_assoc,hr']

/-- The nontrivial compiler permutation is included in this actual gate count. -/
theorem compiledWorkProgram_length (a : ℕ) {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) (external : Bool) :
    (compiledWorkProgram a hμ hr external).length≤36675*(a+1) := by
  have hf := GateSynthesis.lowerProgram_length (mappedPermutation a)
  have hr' := GateSynthesis.lowerProgram_length (mappedPermutation a).reverse
  have hw := WorkGates.workProgram_length a hμ hr external
  simp only [mappedPermutation,mapProgram_length,List.length_reverse] at hf hr'
  change (GateSynthesis.lowerProgram (mappedPermutation a)).length≤90 at hf
  change (GateSynthesis.lowerProgram (mappedPermutation a).reverse).length≤90 at hr'
  simp only [compiledWorkProgram,List.length_append,forwardWorkPermutation,reverseWorkPermutation,List.length_map]
  omega


theorem workInsertion_injective {a : ℕ} (dirty : Bool) :
    Function.Injective (workInsertion (D := D) (a := a) dirty) :=
  (WorkGates.sourceInsertion_injective dirty).comp (rawWorkWiring a D).injective

theorem workInsertion_isometry {a : ℕ} (dirty : Bool) :
    (basisInsertion (workInsertion (D := D) (a := a) dirty))ᴴ*
      basisInsertion (workInsertion (D := D) (a := a) dirty)=1 :=
  basisInsertion_isometry _ (workInsertion_injective dirty)

theorem compiledWorkProgram_coherent {a : ℕ} {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    (external dirty : Bool) (v : WorkSource a D → ℂ) :
    (placedPhaseWord (compiledWorkProgram a hμ hr external)).val *ᵥ
        (basisInsertion (workInsertion dirty) *ᵥ v)=
      basisInsertion (workInsertion dirty) *ᵥ ((compilerSourceWork hμ hr external).val*ᵥv) := by
  rw [Matrix.mulVec_mulVec,compiledWorkProgram_intertwines,Matrix.mulVec_mulVec]

theorem compiledWorkProgram_borrowed_intertwines {a : ℕ} {μ r : ℝ}
    (hμ : 0<μ) (hr : |r|<1) (external : Bool) :
    (placedPhaseWord (D := D) (compiledWorkProgram a hμ hr external)).val *
        basisInsertion (fun x : WorkSource a D × Bool => workInsertion x.2 x.1)=
      basisInsertion (fun x : WorkSource a D × Bool => workInsertion x.2 x.1) *
        (GateSynthesis.placeHom (Equiv.refl (WorkSource a D × Bool))
          (compilerSourceWork hμ hr external)).val := by
  exact WorkGates.intertwines_borrowed_matrix (fun dirty => workInsertion dirty) _ _
    (fun dirty => compiledWorkProgram_intertwines hμ hr external dirty)

theorem compiledWorkProgram_real (a : ℕ) {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    (external : Bool) : ∀ g ∈ compiledWorkProgram a hμ hr external, RealGate g := by
  intro g hg
  simp only [compiledWorkProgram,List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · obtain ⟨h,_,rfl⟩ := List.mem_map.mp hg
    exact GateSynthesis.LowerGate.eval_real h
  · exact WorkGates.workProgram_real a hμ hr external g hg
  · obtain ⟨h,_,rfl⟩ := List.mem_map.mp hg
    exact GateSynthesis.LowerGate.eval_real h

theorem compilerWork_lowered {a : ℕ} {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    (external dirty : Bool) :
    (placedPhaseWord (D := D) (compiledWorkProgram a hμ hr external)).val *
        basisInsertion (workInsertion dirty)=
      basisInsertion (workInsertion dirty)*(compilerSourceWork hμ hr external).val ∧
    (compiledWorkProgram a hμ hr external).length≤36675*(a+1) ∧
    (∀ g ∈ compiledWorkProgram a hμ hr external, g.arity≤2 ∧ RealGate g) := by
  refine ⟨compiledWorkProgram_intertwines hμ hr external dirty,
    compiledWorkProgram_length a hμ hr external,?_⟩
  intro g hg
  exact ⟨PhaseGate.arity_le_two g,compiledWorkProgram_real a hμ hr external g hg⟩

end OptimalQLS.Preparation.CompilerAttachment
