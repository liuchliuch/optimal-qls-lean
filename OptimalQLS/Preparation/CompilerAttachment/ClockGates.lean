import OptimalQLS.TransducerCompiler.LoweredCircuit
import OptimalQLS.PolynomialTransform.DirtyAncilla.LocalPhases
import OptimalQLS.PolynomialTransform.CleanEmbedding

/-! # Literal one-bit Hadamard layers on named clock wires

Every leaf is a physically placed one-qubit Hadamard.  The generic basis
semantics retain all unselected wires and the arbitrary synthesis bit.
-/
noncomputable section
namespace OptimalQLS.Preparation.CompilerAttachment.ClockGates
open Matrix TransducerCompiler PolynomialTransform DirtyAncilla

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The execution list contains one ordinary one-bit Hadamard per clock wire. -/
def code : {ℓ : ℕ} → (Fin ℓ → ι) → List (PhaseGate ι)
  | 0, _ => []
  | _ + 1, f => .single (f 0) HadamardClock.hadamard :: code (fun i => f i.succ)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem code_length {ℓ : ℕ} (f : Fin ℓ → ι) : (code f).length = ℓ := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih => simp [code, ih]

omit [Fintype ι] [DecidableEq ι] in
theorem code_eq_ofFn {ℓ : ℕ} (f : Fin ℓ → ι) :
    code f = List.ofFn (fun i => PhaseGate.single (f i) HadamardClock.hadamard) := by
  induction ℓ with
  | zero => simp [code]
  | succ ℓ ih => simp [code, List.ofFn_succ, ih]

theorem code_real {ℓ : ℕ} (f : Fin ℓ → ι) (g : PhaseGate ι) (hg : g ∈ code f) :
    ∀ i j, (g.eval.val i j).im = 0 := by
  rw [code_eq_ofFn] at hg
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
  exact GateSynthesis.placeHom_real _ _ HadamardClock.hadamard_real

omit [Fintype ι] [DecidableEq ι] in
theorem code_arity {ℓ : ℕ} (f : Fin ℓ → ι) (g : PhaseGate ι) (hg : g ∈ code f) :
    g.arity = 1 := by
  rw [code_eq_ofFn] at hg
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
  rfl

/-- Replace only the explicitly listed clock wires, in their execution order. -/
def setClock : {ℓ : ℕ} → (Fin ℓ → ι) → HadamardClock.Bits ℓ → (ι → Bool) → (ι → Bool)
  | 0, _, _, b => b
  | _ + 1, f, x, b => setClock (fun i => f i.succ) (Fin.tail x)
      (Function.update b (f 0) (x 0))

omit [Fintype ι] in
theorem setClock_outside {ℓ : ℕ} (f : Fin ℓ → ι) (x : HadamardClock.Bits ℓ)
    (b : ι → Bool) (j : ι) (hj : ∀ i, f i ≠ j) : setClock f x b j = b j := by
  induction ℓ generalizing b with
  | zero => rfl
  | succ ℓ ih =>
    rw [setClock, ih _ _ _ (fun i => hj i.succ)]
    exact Function.update_of_ne (Ne.symm (hj 0)) _ _

omit [Fintype ι] in
theorem setClock_selected {ℓ : ℕ} (f : Fin ℓ → ι) (hf : Function.Injective f)
    (x : HadamardClock.Bits ℓ) (b : ι → Bool) (i : Fin ℓ) : setClock f x b (f i) = x i := by
  induction ℓ generalizing b with
  | zero => exact Fin.elim0 i
  | succ ℓ ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [setClock, setClock_outside]
      · simp
      · intro j h
        exact Fin.succ_ne_zero j (hf h)
    · exact ih _ (hf.comp (Fin.succ_injective _)) _ _ i

/-- One selected-bit gate has exactly the two standard basis branches. -/
theorem single_basis (t : ι) (U : Matrix.unitaryGroup Bool ℂ) (z : Bool) (b : ι → Bool) :
    (PhaseGate.single t U).eval.val *ᵥ Pi.single (z,b) 1 =
      ∑ y : Bool, U.val y (b t) •
        (Pi.single (z, Function.update b t y) 1 : GateSynthesis.Space ι → ℂ) := by
  change (GateSynthesis.placeHom (singleWiring t) U).val *ᵥ _ = _
  have hi : singleWiring t (b t, (z, fun i => b i.val)) = (z,b) :=
    (singleWiring t).apply_symm_apply (z,b)
  conv_lhs => rw [← hi]
  rw [placeHom_basis_sum]
  apply Finset.sum_congr rfl
  intro y _
  congr 2
  apply Prod.ext
  · rfl
  · funext j
    simp [singleWiring, Function.update_apply]

/-- Exact coherent clock action, with all nonclock bits and the synthesis bit
untouched.  Injectivity is solely a distinct-wire condition. -/
theorem code_basis {ℓ : ℕ} (f : Fin ℓ → ι) (hf : Function.Injective f)
    (z : Bool) (b : ι → Bool) :
    (phaseEval (code f)).val *ᵥ Pi.single (z,b) 1 =
      ∑ x : HadamardClock.Bits ℓ,
        (HadamardClock.tensorHadamard ℓ).val x (fun i => b (f i)) •
          (Pi.single (z, setClock f x b) 1 : GateSynthesis.Space ι → ℂ) := by
  induction ℓ generalizing b with
  | zero =>
    have hh : (HadamardClock.tensorHadamard 0).val = fun _ _ => (1 : ℂ) := by
      ext x y
      have hxy : x = y := Subsingleton.elim _ _
      simp [HadamardClock.tensorHadamard, HadamardClock.circuit,
        HadamardClock.Circuit.eval, hxy]
    change (1 : Matrix (GateSynthesis.Space ι) (GateSynthesis.Space ι) ℂ) *ᵥ _ = _
    rw [Matrix.one_mulVec]
    simp only [hh, one_smul, Fintype.sum_unique, setClock]
  | succ ℓ ih =>
    simp only [code, phaseEval, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    rw [single_basis, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
    simp_rw [ih (fun i : Fin ℓ => f i.succ) (hf.comp (Fin.succ_injective _))]
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ => Bool)), Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro x _
    have hb : (fun i : Fin ℓ => Function.update b (f 0) y (f i.succ)) =
        (fun i : Fin ℓ => b (f i.succ)) := by
      funext i
      exact Function.update_of_ne (fun h => Fin.succ_ne_zero i (hf h)) _ _
    rw [hb, smul_smul]
    rfl

theorem setClock_id {ℓ : ℕ} (x b : HadamardClock.Bits ℓ) :
    setClock (fun i : Fin ℓ => i) x b = x := by
  funext i
  exact setClock_selected _ Function.injective_id _ _ i

/-- On a standalone clock register the actual gate list is precisely the
tensor-Hadamard unitary, tensored with the arbitrary synthesis bit. -/
theorem code_eval (ℓ : ℕ) :
    phaseEval (code (fun i : Fin ℓ => i)) =
      GateSynthesis.dataHom (HadamardClock.tensorHadamard ℓ) := by
  apply Subtype.ext
  apply Matrix.ext_of_mulVec_single
  rintro ⟨z,b⟩
  rw [code_basis (fun i : Fin ℓ => i) Function.injective_id]
  change _ = (GateSynthesis.placeHom (Equiv.prodComm (HadamardClock.Bits ℓ) Bool)
    (HadamardClock.tensorHadamard ℓ)).val *ᵥ Pi.single
      ((Equiv.prodComm (HadamardClock.Bits ℓ) Bool) (b,z)) 1
  rw [placeHom_basis_sum]
  simp only [setClock_id, Equiv.prodComm_apply]
  rfl

/-- Coordinate-level interface for embedding the literal clock layer into a
larger compiler frame.  The hypotheses state which named wires hold the clock
bits and that replacing these bits leaves the complete spectator frame alone. -/
theorem code_intertwines {ℓ : ℕ} (f : Fin ℓ → ι) (hf : Function.Injective f)
    {L D : Type*} [Fintype L] [DecidableEq L] [Fintype D] [DecidableEq D]
    (e : HadamardClock.Bits ℓ × D ≃ L) (k : L → GateSynthesis.Space ι)
    (hclock : ∀ x d i, (k (e (x,d))).2 (f i) = x i)
    (hset : ∀ x y d, ((k (e (x,d))).1, setClock f y (k (e (x,d))).2) = k (e (y,d))) :
    (phaseEval (code f)).val * basisInsertion k = basisInsertion k *
      (GateSynthesis.placeHom e (HadamardClock.tensorHadamard ℓ)).val := by
  apply basisInsertion_intertwines
  intro l
  obtain ⟨⟨x,d⟩,rfl⟩ := e.surjective l
  rw [code_basis f hf, placeHom_basis_sum, Matrix.mulVec_sum]
  have hb : (fun i => (k (e (x,d))).2 (f i)) = x := funext (hclock x d)
  rw [hb]
  apply Finset.sum_congr rfl
  intro y _
  rw [Matrix.mulVec_smul, basisInsertion_basis, hset]

/-- A complete named-wire decomposition gives exact equality of the full
unitaries, without any cleanliness assumption on any spectator. -/
theorem code_eq_placeHom {ℓ : ℕ} (f : Fin ℓ → ι) (hf : Function.Injective f)
    {D : Type*} [Fintype D] [DecidableEq D]
    (e : HadamardClock.Bits ℓ × D ≃ GateSynthesis.Space ι)
    (hclock : ∀ x d i, (e (x,d)).2 (f i) = x i)
    (hset : ∀ x y d, ((e (x,d)).1, setClock f y (e (x,d)).2) = e (y,d)) :
    phaseEval (code f) = GateSynthesis.placeHom e (HadamardClock.tensorHadamard ℓ) := by
  apply Subtype.ext
  apply Matrix.ext_of_mulVec_single
  intro l
  obtain ⟨⟨x,d⟩,rfl⟩ := e.surjective l
  rw [code_basis f hf, placeHom_basis_sum]
  have hb : (fun i => (e (x,d)).2 (f i)) = x := funext (hclock x d)
  rw [hb]
  apply Finset.sum_congr rfl
  intro y _
  rw [hset]

open BinaryClock

/-- Clock bit `i` is exactly the existing compiler wire `inr (inl i)`. -/
def labelClockWire (ℓ : ℕ) (i : Fin ℓ) : LabelWire ℓ := .inr (.inl i)

theorem labelClockWire_injective (ℓ : ℕ) : Function.Injective (labelClockWire ℓ) := by
  intro i j h
  simpa only [labelClockWire, Sum.inr.injEq, Sum.inl.injEq] using h

def labelCode (ℓ : ℕ) : List (PhaseGate (LabelWire ℓ)) := code (labelClockWire ℓ)

/-- The clock, label, cache, and synthesis registers are merely regrouped;
this equivalence is used only to state the meaning of the literal leaves. -/
def labelClockWiring (ℓ : ℕ) :
    HadamardClock.Bits ℓ × (Bool × (Label × Bits ℓ)) ≃ GateSynthesis.Space (LabelWire ℓ) where
  toFun p := (p.2.1, labelStateEquiv.symm (p.2.2.1,p.1,p.2.2.2))
  invFun b := ((labelStateEquiv b.2).2.1,b.1,(labelStateEquiv b.2).1,(labelStateEquiv b.2).2.2)
  left_inv p := by rcases p with ⟨x,z,l,a⟩; simp
  right_inv b := by rcases b with ⟨z,b⟩; simp

theorem labelClockWiring_read (ℓ : ℕ) (x : HadamardClock.Bits ℓ)
    (d : Bool × (Label × Bits ℓ)) (i : Fin ℓ) :
    (labelClockWiring ℓ (x,d)).2 (labelClockWire ℓ i) = x i := rfl

theorem labelClockWiring_set (ℓ : ℕ) (x y : HadamardClock.Bits ℓ)
    (d : Bool × (Label × Bits ℓ)) :
    ((labelClockWiring ℓ (x,d)).1,
      setClock (labelClockWire ℓ) y (labelClockWiring ℓ (x,d)).2) =
        labelClockWiring ℓ (y,d) := by
  apply Prod.ext
  · rfl
  · funext w
    change setClock (labelClockWire ℓ) y (labelClockWiring ℓ (x,d)).2 w =
      (labelClockWiring ℓ (y,d)).2 w
    cases w with
    | inl i =>
      rw [setClock_outside]
      · rfl
      · intro j h; cases h
    | inr w =>
      cases w with
      | inl i => exact setClock_selected _ (labelClockWire_injective ℓ) _ _ i
      | inr i =>
        rw [setClock_outside]
        · rfl
        · intro j h; cases h

theorem labelCode_eval (ℓ : ℕ) :
    phaseEval (labelCode ℓ) =
      GateSynthesis.placeHom (labelClockWiring ℓ) (HadamardClock.tensorHadamard ℓ) :=
  code_eq_placeHom _ (labelClockWire_injective ℓ) _
    (labelClockWiring_read ℓ) (labelClockWiring_set ℓ)

theorem tensorHadamard_inv (ℓ : ℕ) :
    (HadamardClock.tensorHadamard ℓ)⁻¹ = HadamardClock.tensorHadamard ℓ := by
  apply Subtype.ext
  exact HadamardClock.tensorHadamard_selfAdjoint ℓ

theorem finHadamard_inv (ℓ : ℕ) :
    (HadamardClock.finHadamard ℓ)⁻¹ = HadamardClock.finHadamard ℓ := by
  apply Subtype.ext
  exact HadamardClock.finHadamard_selfAdjoint ℓ

theorem clockLift_hadamard_inv {n : Type*} [Fintype n] [DecidableEq n] (ℓ : ℕ) :
    (clockLift (n := n) (HadamardClock.finHadamard ℓ))⁻¹ =
      clockLift (n := n) (HadamardClock.finHadamard ℓ) := by
  change (GateSynthesis.placeHom (Equiv.prodComm (Fin (2^ℓ)) (Base n))
    (HadamardClock.finHadamard ℓ))⁻¹ =
      GateSynthesis.placeHom (Equiv.prodComm (Fin (2^ℓ)) (Base n))
        (HadamardClock.finHadamard ℓ)
  rw [← map_inv, finHadamard_inv]

theorem placeHom_entries {A D P : Type*} [Fintype A] [DecidableEq A]
    [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]
    (e : A × D ≃ P) (U : Matrix.unitaryGroup A ℂ) (p q : P) :
    (GateSynthesis.placeHom e U).val p q =
      if (e.symm p).2 = (e.symm q).2 then U.val (e.symm p).1 (e.symm q).1 else 0 := rfl

theorem synthWiring_symm_entries {n : Type*} {ℓ : ℕ}
    (z : Bool) (d : n) (l : Label) (x a : Bits ℓ) :
    (synthWiring (n := n) (ℓ := ℓ)).symm (z,(d,l),x,a) =
      ((z,labelStateEquiv.symm (l,x,a)),d) := rfl

theorem labelClockWiring_symm_entries (ℓ : ℕ)
    (z : Bool) (l : Label) (x a : Bits ℓ) :
    (labelClockWiring ℓ).symm (z,labelStateEquiv.symm (l,x,a)) = (x,z,l,a) := by
  change ((labelStateEquiv (labelStateEquiv.symm (l,x,a))).2.1,z,
    (labelStateEquiv (labelStateEquiv.symm (l,x,a))).1,
    (labelStateEquiv (labelStateEquiv.symm (l,x,a))).2.2) = _
  simp only [Equiv.apply_symm_apply]

/-- Both clock instructions in the actual synthesized compiler are expanded
by this same literal list, on every basis state, with no clean-bit hypothesis. -/
theorem labelCode_synth_eval {n : Type*} [Fintype n] [DecidableEq n] (ℓ : ℕ)
    (S : Matrix.unitaryGroup (Base n) ℂ) (U₁ U₂ : Matrix.unitaryGroup n ℂ) (adj : Bool) :
    lowerAuxHom (n := n) (phaseEval (labelCode ℓ)) =
      (SynthInstruction.clock adj).eval S U₁ U₂ := by
  rw [labelCode_eval]
  have hi : (if adj then (clockLift (n := n) (HadamardClock.finHadamard ℓ))⁻¹
      else clockLift (n := n) (HadamardClock.finHadamard ℓ)) =
        clockLift (n := n) (HadamardClock.finHadamard ℓ) := by
    cases adj <;> simp [clockLift_hadamard_inv]
  simp only [SynthInstruction.eval, hi]
  apply Subtype.ext
  ext ⟨z,⟨d,l⟩,x,a⟩ ⟨w,⟨d',l'⟩,y,a'⟩
  simp only [lowerAuxHom, padHom, placeHom_entries]
  simp only [synthWiring_symm_entries, labelClockWiring_symm_entries, Prod.fst, Prod.snd]
  change (if d=d' then
      (if (z,l,a)=(w,l',a') then (HadamardClock.tensorHadamard ℓ).val x y else 0) else 0) =
    (if z=w then (if a=a' then (if (d,l)=(d',l') then
      (HadamardClock.tensorHadamard ℓ).val
        ((HadamardClock.bitsFinEquiv ℓ).symm (HadamardClock.bitsFinEquiv ℓ x))
        ((HadamardClock.bitsFinEquiv ℓ).symm (HadamardClock.bitsFinEquiv ℓ y))
      else 0) else 0) else 0)
  simp only [Equiv.symm_apply_apply, Prod.mk.injEq]
  by_cases hd : d=d' <;> by_cases hl : l=l' <;> by_cases hz : z=w <;>
    by_cases ha : a=a' <;> simp [hd, hl, hz, ha]

end OptimalQLS.Preparation.CompilerAttachment.ClockGates
