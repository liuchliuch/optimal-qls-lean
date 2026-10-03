import OptimalQLS.Preparation.ControlledTarget
import OptimalQLS.GraphEncoding.SmallGates

/-! # Literal mixed-polarity one-qubit control macros -/
noncomputable section
namespace OptimalQLS.Preparation.WorkGates
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def positiveWires (n : ℕ) (f : SmallWire n → ι) (p : ι → Bool) : List ι :=
  (List.ofFn (fun i : Fin n => f (.inl i))).filter p

def patternFlip (n : ℕ) (f : SmallWire n → ι) (p : ι → Bool) : Program ι :=
  (positiveWires n f p).map Gate.x

theorem positiveWires_nodup (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (p : ι → Bool) : (positiveWires n f p).Nodup := by
  apply List.Nodup.filter
  exact List.nodup_ofFn.mpr (hf.comp Sum.inl_injective)

theorem mem_positiveWires (n : ℕ) (f : SmallWire n → ι) (p : ι → Bool) (j : ι) :
    j ∈ positiveWires n f p ↔ (∃ i : Fin n, f (.inl i)=j) ∧ p j=true := by
  simp [positiveWires,List.mem_ofFn]

theorem patternFlip_run (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (p : ι → Bool) (b : ι → Bool) (j : ι) :
    run (patternFlip n f p) b j = if j ∈ positiveWires n f p then !(b j) else b j :=
  flipList_run _ (positiveWires_nodup n f hf p) b j

theorem patternFlip_flag (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (p : ι → Bool) (b : ι → Bool) :
    run (patternFlip n f p) b (f (smallTarget n))=b (f (smallTarget n)) := by
  rw [patternFlip_run n f hf]
  simp [mem_positiveWires,hf.eq_iff,smallTarget]

theorem patternFlip_control (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (p : ι → Bool) (b : ι → Bool) (i : Fin n) :
    run (patternFlip n f p) b (f (.inl i)) =
      if p (f (.inl i)) then !(b (f (.inl i))) else b (f (.inl i)) := by
  rw [patternFlip_run n f hf]
  simp [mem_positiveWires,hf.eq_iff]

theorem patternFlip_test (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (p : ι → Bool) (b : ι → Bool) :
    (∀ i : Fin n, run (patternFlip n f p) b (f (.inl i))=false) ↔
      ∀ i : Fin n, b (f (.inl i))=p (f (.inl i)) := by
  apply forall_congr'
  intro i
  rw [patternFlip_control n f hf]
  cases p (f (.inl i)) <;> cases b (f (.inl i)) <;> simp

theorem patternFlip_target (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (p : ι → Bool) (t : ι) (ht : ∀ i : Fin n, f (.inl i)≠t) (b : ι → Bool) :
    run (patternFlip n f p) b t=b t := by
  rw [patternFlip_run n f hf]
  simp [mem_positiveWires,ht]

theorem patternFlip_target_update (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (p : ι → Bool) (t : ι) (ht : ∀ i : Fin n, f (.inl i)≠t) (b : ι → Bool) (y : Bool) :
    run (patternFlip n f p) (Function.update b t y)=
      Function.update (run (patternFlip n f p) b) t y := by
  funext j
  by_cases h : j=t
  · subst j
    rw [patternFlip_target n f hf p t ht]
    simp
  · simp only [patternFlip_run n f hf,Function.update_of_ne h]

def patternControlledTarget (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (t : ι) (hft : f (smallTarget n)≠t) (p : ι → Bool)
    (U : Matrix.unitaryGroup Bool ℂ) : List (PhaseGate ι) :=
  (GateSynthesis.lowerProgram (patternFlip n f p)).map PhaseGate.real ++
    zeroControlledTarget n f hf t hft U ++
    (GateSynthesis.lowerProgram (patternFlip n f p).reverse).map PhaseGate.real

theorem patternControlledTarget_length (n : ℕ) (f : SmallWire n → ι)
    (hf : Function.Injective f) (t : ι) (hft : f (smallTarget n)≠t) (p : ι → Bool)
    (U : Matrix.unitaryGroup Bool ℂ) :
    (patternControlledTarget n f hf t hft p U).length ≤ 811*(n+1) := by
  have h := GateSynthesis.lowerProgram_length (patternFlip n f p)
  have h' := GateSynthesis.lowerProgram_length (patternFlip n f p).reverse
  have hz := zeroControlledTarget_length n f hf t hft U
  have hp : (patternFlip n f p).length ≤ n := by
    simpa only [patternFlip,List.length_map,positiveWires,List.length_ofFn] using
      (List.length_filter_le (p := p) (l := List.ofFn (fun i : Fin n => f (.inl i))))
  simp only [List.length_reverse] at h'
  simp only [patternControlledTarget,List.length_append,List.length_map]
  omega

/-- Every signal string, every label, and the arbitrary borrowed bit are included.
Only the flag and the common Toffoli-synthesis bit are assumed clean. -/
theorem patternControlledTarget_basis (n : ℕ) (f : SmallWire n → ι)
    (hf : Function.Injective f) (t : ι) (hft : f (smallTarget n)≠t)
    (ht : ∀ i : Fin n, f (.inl i)≠t) (p : ι → Bool)
    (U : Matrix.unitaryGroup Bool ℂ) (b : ι → Bool) (hb : b (f (smallTarget n))=false) :
    (phaseEval (patternControlledTarget n f hf t hft p U)).val *ᵥ Pi.single (false,b) 1 =
      ∑ y : Bool,
        (if decide (∀ i : Fin n, b (f (.inl i))=p (f (.inl i))) then U.val y (b t)
          else if y=b t then 1 else 0) •
        (Pi.single (false,Function.update b t y) 1 : GateSynthesis.Space ι → ℂ) := by
  simp only [patternControlledTarget,phaseEval_append,phaseEval_real,Submonoid.coe_mul,
    ← Matrix.mulVec_mulVec]
  rw [GateSynthesis.lowerProgram_basis]
  rw [zeroControlledTarget_basis n f hf t hft ht U _ (by rw [patternFlip_flag n f hf]; exact hb)]
  rw [Matrix.mulVec_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [Matrix.mulVec_smul,GateSynthesis.lowerProgram_basis,
    ← patternFlip_target_update n f hf p t ht,run_reverse_run]
  simp only [patternFlip_test n f hf,patternFlip_target n f hf p t ht]

/-- Real one-qubit matrices give real two-qubit control matrices. -/
theorem controlledTarget_real (U : Matrix.unitaryGroup Bool ℂ)
    (hU : ∀ i j, (U.val i j).im=0) (i j : Bool × Bool) :
    ((controlledTargetUnitary U).val i j).im=0 := by
  rw [controlledTarget_entries]
  split_ifs <;> simp [hU]

def RealGate (g : PhaseGate ι) : Prop := ∀ i j, (g.eval.val i j).im=0

theorem patternControlledTarget_real (n : ℕ) (f : SmallWire n → ι)
    (hf : Function.Injective f) (t : ι) (hft : f (smallTarget n)≠t) (p : ι → Bool)
    (U : Matrix.unitaryGroup Bool ℂ) (hU : ∀ i j, (U.val i j).im=0) :
    ∀ g ∈ patternControlledTarget n f hf t hft p U, RealGate g := by
  intro g hg
  have hr (l : List (GateSynthesis.LowerGate ι)) :
      ∀ k ∈ l.map PhaseGate.real, RealGate k := by
    intro k hk
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hk
    exact GateSynthesis.LowerGate.eval_real _
  have hp : RealGate (.pair (f (smallTarget n)) t hft (controlledTargetUnitary U)) :=
    GateSynthesis.placeHom_real _ _ (controlledTarget_real U hU)
  simp only [patternControlledTarget,zeroControlledTarget,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false] at hg
  aesop

end OptimalQLS.Preparation.WorkGates
