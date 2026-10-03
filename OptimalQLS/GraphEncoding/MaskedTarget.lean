import OptimalQLS.Preparation.ControlledTarget
import OptimalQLS.GraphEncoding.ElementaryLocality

/-! # Literal-mask controls for one-qubit target gates -/
noncomputable section
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 1000000
namespace OptimalQLS.GraphEncoding
open Matrix TransducerCompiler BinaryClock
open PolynomialTransform DirtyAncilla Preparation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The polarity corrections are X gates only on tested physical wires. -/
def maskFlipList (n : ℕ) (f : SmallWire n → ι) (mask : Fin n → Bool) : List ι :=
  (List.ofFn (fun i : Fin n => f (.inl i))).filter (fun j =>
    decide (∃ i : Fin n, f (.inl i)=j ∧ mask i=true))

theorem maskFlipList_nodup (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (mask : Fin n → Bool) : (maskFlipList n f mask).Nodup :=
  (List.nodup_ofFn.mpr (hf.comp Sum.inl_injective)).filter _

theorem maskFlipList_mem (n : ℕ) (f : SmallWire n → ι) (mask : Fin n → Bool) (j : ι) :
    j ∈ maskFlipList n f mask ↔ ∃ i : Fin n, f (.inl i)=j ∧ mask i=true := by
  simp only [maskFlipList, List.mem_filter, List.mem_ofFn, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun ⟨i,hi,hm⟩ => ⟨⟨i,hi⟩,⟨i,hi,hm⟩⟩⟩

def maskFlipProgram (n : ℕ) (f : SmallWire n → ι) (mask : Fin n → Bool) : Program ι :=
  (maskFlipList n f mask).map BinaryClock.Gate.x

theorem maskFlipProgram_apply (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (mask : Fin n → Bool) (b : ι → Bool) (j : ι) :
    run (maskFlipProgram n f mask) b j =
      if j ∈ maskFlipList n f mask then !(b j) else b j :=
  flipList_run _ (maskFlipList_nodup n f hf mask) b j

theorem maskFlipProgram_control (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (mask : Fin n → Bool) (b : ι → Bool) (i : Fin n) :
    run (maskFlipProgram n f mask) b (f (.inl i)) = Bool.xor (b (f (.inl i))) (mask i) := by
  rw [maskFlipProgram_apply n f hf]
  simp only [maskFlipList_mem]
  have he : (∃ j : Fin n, f (.inl j)=f (.inl i) ∧ mask j=true) ↔ mask i=true := by
    simp [hf.eq_iff]
  simp only [he]
  cases mask i <;> cases b (f (.inl i)) <;> rfl

theorem maskFlipProgram_other (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (mask : Fin n → Bool) (b : ι → Bool) (j : ι)
    (hj : ∀ i : Fin n, f (.inl i)≠j) : run (maskFlipProgram n f mask) b j = b j := by
  rw [maskFlipProgram_apply n f hf, if_neg]
  simp only [maskFlipList_mem]
  rintro ⟨i,hi,_⟩
  exact hj i hi

theorem maskFlipProgram_twice (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (mask : Fin n → Bool) (b : ι → Bool) :
    run (maskFlipProgram n f mask) (run (maskFlipProgram n f mask) b)=b := by
  ext j
  simp only [maskFlipProgram_apply n f hf]
  split_ifs <;> simp

theorem maskFlipProgram_update (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (mask : Fin n → Bool) (b : ι → Bool) (t : ι)
    (ht : ∀ i : Fin n, f (.inl i)≠t) (y : Bool) :
    run (maskFlipProgram n f mask) (Function.update b t y) =
      Function.update (run (maskFlipProgram n f mask) b) t y := by
  ext j
  by_cases hj : j=t
  · subst j
    rw [maskFlipProgram_other n f hf mask _ _ ht]
    simp
  · simp only [maskFlipProgram_apply n f hf, Function.update_of_ne hj]

def maskedTarget (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (t : ι) (hft : f (smallTarget n)≠t) (mask : Fin n → Bool)
    (U : Matrix.unitaryGroup Bool ℂ) : List (PhaseGate ι) :=
  (TransducerCompiler.GateSynthesis.lowerProgram (maskFlipProgram n f mask)).map PhaseGate.real ++
  zeroControlledTarget n f hf t hft U ++
  (TransducerCompiler.GateSynthesis.lowerProgram (maskFlipProgram n f mask)).map PhaseGate.real

theorem maskFlipProgram_length (n : ℕ) (f : SmallWire n → ι) (mask : Fin n → Bool) :
    (maskFlipProgram n f mask).length ≤ n := by
  simpa only [maskFlipProgram, List.length_map, maskFlipList, List.length_ofFn] using
    List.length_filter_le (fun j => decide (∃ i : Fin n, f (.inl i)=j ∧ mask i=true))
      (List.ofFn (fun i : Fin n => f (.inl i)))

/-- At most3214 actual elementary gates for any three literal controls. -/
theorem maskedTarget_length (n : ℕ) (hn : n ≤ 3) (f : SmallWire n → ι)
    (hf : Function.Injective f) (t : ι) (hft : f (smallTarget n)≠t)
    (mask : Fin n → Bool) (U : Matrix.unitaryGroup Bool ℂ) :
    (maskedTarget n f hf t hft mask U).length ≤ 3214 := by
  have h := TransducerCompiler.GateSynthesis.lowerProgram_length (maskFlipProgram n f mask)
  have hf' := maskFlipProgram_length n f mask
  have hz := zeroControlledTarget_length n f hf t hft U
  simp only [maskedTarget, List.length_append, List.length_map]
  omega

/-- Exact coherent masked action, with the synthesis bit and zero-test flag
restored, and arbitrary borrowed/spectator inputs unchanged. -/
theorem maskedTarget_basis (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (t : ι) (hft : f (smallTarget n)≠t) (ht : ∀ i : Fin n, f (.inl i)≠t)
    (mask : Fin n → Bool) (U : Matrix.unitaryGroup Bool ℂ) (b : ι → Bool)
    (hb : b (f (smallTarget n))=false) :
    (phaseEval (maskedTarget n f hf t hft mask U)).val *ᵥ Pi.single (false,b) 1 =
      ∑ y : Bool,
        (if decide (∀ i : Fin n, b (f (.inl i))=mask i) then U.val y (b t)
          else if y=b t then 1 else 0) •
        (Pi.single (false,Function.update b t y) 1 : TransducerCompiler.GateSynthesis.Space ι → ℂ) := by
  have hb' : run (maskFlipProgram n f mask) b (f (smallTarget n))=false := by
    rw [maskFlipProgram_other n f hf]
    · exact hb
    · intro i hi
      have hh := hf hi
      cases hh
  have ht' := maskFlipProgram_other n f hf mask b t ht
  have hp : (∀ i : Fin n, run (maskFlipProgram n f mask) b (f (.inl i))=false) ↔
      (∀ i : Fin n, b (f (.inl i))=mask i) := by
    simp only [maskFlipProgram_control n f hf]
    apply forall_congr'
    intro i
    cases b (f (.inl i)) <;> cases mask i <;> simp
  simp only [maskedTarget, phaseEval_append, phaseEval_real, Submonoid.coe_mul,
    ← Matrix.mulVec_mulVec]
  rw [TransducerCompiler.GateSynthesis.lowerProgram_basis,
    zeroControlledTarget_basis n f hf t hft ht U _ hb', Matrix.mulVec_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [Matrix.mulVec_smul, TransducerCompiler.GateSynthesis.lowerProgram_basis,
    maskFlipProgram_update n f hf mask _ t ht, maskFlipProgram_twice n f hf]
  simp only [hp, ht']

end OptimalQLS.GraphEncoding
