import OptimalQLS.Preparation.CompilerAttachment.MaskedPhase
import OptimalQLS.Preparation.WorkGates.Refinement
import OptimalQLS.GraphEncoding.AllowedCalls
import OptimalQLS.PolynomialTransform.PhysicalRegister

/-! # Actual controlled source-basis reflection with data-linear gate cost -/
noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace OptimalQLS.Preparation.CompilerAttachment
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla

abbrev ReflectionBit (n : ℕ) := Fin 4 ⊕ Fin n
abbrev ReflectionWire (n : ℕ) := ReflectionBit n ⊕ Fin 2
abbrev ReflectionState (n : ℕ) := GateSynthesis.Space (ReflectionWire n)
abbrev ReflectionSource (n : ℕ) := (Bool × Bool) × (Fin 4 × Bits n)

/-- Two compiler-label bits, two graph-label bits, then the actual n data bits. -/
def reflectionBitsEquiv (n : ℕ) : (ReflectionBit n → Bool) ≃ ReflectionSource n where
  toFun b := ((b (.inl 0),b (.inl 1)),
    GraphEncoding.graphBits (b (.inl 2),b (.inl 3)),fun i=>b (.inr i))
  invFun p := Sum.elim ![p.1.1,p.1.2,(GraphEncoding.graphBits.symm p.2.1).1,
    (GraphEncoding.graphBits.symm p.2.1).2] p.2.2
  left_inv b := by
    funext i
    cases i with
    | inl i => fin_cases i <;> simp
    | inr i => rfl
  right_inv p := by
    rcases p with ⟨⟨a,b⟩,g,d⟩
    simp

/-- Pure coordinate regrouping; the three extra bits are precisely exposed. -/
def reflectionRegister (n : ℕ) : ReflectionSource n × PhaseScratch ≃ ReflectionState n where
  toFun p := (p.2.1,Sum.elim ((reflectionBitsEquiv n).symm p.1)
    (fun i=>if i=0 then p.2.2.1 else p.2.2.2))
  invFun p := (reflectionBitsEquiv n (fun i=>p.2 (.inl i)),p.1,p.2 (.inr 0),p.2 (.inr 1))
  left_inv p := by
    rcases p with ⟨x,z,f,r⟩
    simp
  right_inv p := by
    rcases p with ⟨z,b⟩
    apply Prod.ext
    · rfl
    · funext i
      cases i with
      | inl i => exact congrFun ((reflectionBitsEquiv n).symm_apply_apply (fun j=>b (.inl j))) i
      | inr i => fin_cases i <;> rfl

def reflectionClean (n : ℕ) (x : ReflectionSource n) : ReflectionState n :=
  reflectionRegister n (x,(false,false,false))

def reflectionLabelControls (n : ℕ) : SmallWire 2 → ReflectionWire n
  | .inl i => .inl (.inl (Fin.castLE (by omega : 2≤4) i))
  | .inr i => .inr i

theorem reflectionLabelControls_injective (n : ℕ) :
    Function.Injective (reflectionLabelControls n) := by
  intro i j h
  cases i <;> cases j <;> simp_all [reflectionLabelControls,Fin.ext_iff]

def reflectionPointMask (n : ℕ) : ReflectionBit n → Bool :=
  Sum.elim ![true,true,false,true] (fun _=>false)

def reflectionPointControls (n : ℕ) : SmallWire (Fintype.card (ReflectionBit n)) → ReflectionWire n :=
  WorkGates.controlWiring (Fintype.equivFin (ReflectionBit n)).symm

theorem reflectionPointControls_injective (n : ℕ) :
    Function.Injective (reflectionPointControls n) :=
  WorkGates.controlWiring_injective _ (Equiv.injective _)

def reflectionPhaseCode (n : ℕ) : List (PhaseGate (ReflectionWire n)) :=
  maskedPhaseCode 2 (reflectionLabelControls n) (reflectionLabelControls_injective n)
    (fun _=>true) matchSign ++
  maskedPhaseCode (Fintype.card (ReflectionBit n)) (reflectionPointControls n)
    (reflectionPointControls_injective n)
    (fun i=>reflectionPointMask n ((Fintype.equivFin (ReflectionBit n)).symm i)) matchSign

/-- This is a length bound on the two emitted phase-test words, independent of signal size. -/
theorem reflectionPhaseCode_length (n : ℕ) :
    (reflectionPhaseCode n).length ≤ 6422*(n+1) := by
  have h₁ := maskedPhaseCode_length 2 (reflectionLabelControls n)
    (reflectionLabelControls_injective n) (fun _=>true) matchSign
  have h₂ := maskedPhaseCode_length (Fintype.card (ReflectionBit n)) (reflectionPointControls n)
    (reflectionPointControls_injective n)
    (fun i=>reflectionPointMask n ((Fintype.equivFin (ReflectionBit n)).symm i)) matchSign
  simp only [reflectionPhaseCode,List.length_append]
  have h₂' := h₂.trans (show 30*(Fintype.card (ReflectionBit n)+26*(Fintype.card (ReflectionBit n)+1))+1 ≤ 810*n+4021 by
    simp only [ReflectionBit,Fintype.card_sum,Fintype.card_fin]; omega)
  omega

theorem reflectionPhaseCode_real (n : ℕ) :
    ∀ g ∈ reflectionPhaseCode n, GraphEncoding.RealPhaseGate g := by
  intro g hg
  rcases List.mem_append.mp hg with hg|hg
  · exact maskedPhaseCode_real _ _ _ _ g hg
  · exact maskedPhaseCode_real _ _ _ _ g hg

theorem reflectionLabel_matches (n : ℕ) (x : ReflectionSource n) :
    (∀ i : Fin 2, (reflectionClean n x).2 (reflectionLabelControls n (.inl i))=true) ↔
      x.1=(true,true) := by
  rcases x with ⟨⟨a,b⟩,g,d⟩
  simp [reflectionClean,reflectionRegister,reflectionBitsEquiv,reflectionLabelControls,
    Fin.forall_fin_succ,Prod.mk.injEq]

theorem reflectionPoint_matches (n : ℕ) (x : ReflectionSource n) :
    (∀ i : Fin (Fintype.card (ReflectionBit n)),
      (reflectionClean n x).2 (reflectionPointControls n (.inl i))=
        reflectionPointMask n ((Fintype.equivFin (ReflectionBit n)).symm i)) ↔
      x.1=(true,true) ∧ x.2=(1,fun _=>false) := by
  have he : (∀ i : Fin (Fintype.card (ReflectionBit n)),
      (reflectionClean n x).2 (reflectionPointControls n (.inl i))=
        reflectionPointMask n ((Fintype.equivFin (ReflectionBit n)).symm i)) ↔
      (reflectionBitsEquiv n).symm x=reflectionPointMask n := by
    constructor
    · intro h
      funext i
      simpa [reflectionClean,reflectionRegister,reflectionPointControls,
        WorkGates.controlWiring] using h ((Fintype.equivFin (ReflectionBit n)) i)
    · intro h i
      exact congrFun h ((Fintype.equivFin (ReflectionBit n)).symm i)
  rw [he,Equiv.symm_apply_eq]
  simp [reflectionBitsEquiv,reflectionPointMask,GraphEncoding.graphBits,Prod.ext_iff]

def reflectionPhaseUnitary (n : ℕ) : Matrix.unitaryGroup (ReflectionSource n) ℂ :=
  (GraphEncoding.maskedGraphPort (Fin 4 × Bits n) (true,true)).apply
    (basisStateReflection (1,fun _=>false))

/-- The controlled reflection fixes graph-label1/data0 and negates its complement
only in the compiler's second-query sector. -/
theorem reflectionPhaseUnitary_basis (n : ℕ) (x : ReflectionSource n) :
    (reflectionPhaseUnitary n).val *ᵥ Pi.single x 1 =
      (if x.1=(true,true) then (if x.2=(1,fun _=>false) then (1:ℂ) else -1) else 1) •
        (Pi.single x 1 : ReflectionSource n→ℂ) := by
  ext y
  rcases x with ⟨m,x⟩
  rcases y with ⟨k,y⟩
  simp only [Matrix.mulVec_single_one,Matrix.col_apply,reflectionPhaseUnitary,
    GraphEncoding.maskedGraphPort_apply_entries,basisStateReflection,
    Matrix.diagonal_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
  by_cases hk : k=m <;> by_cases hy : y=x <;> subst_vars <;>
    simp_all [Prod.mk.injEq]

theorem reflectionPhaseCode_basis (n : ℕ) (x : ReflectionSource n) :
    (phaseEval (reflectionPhaseCode n)).val *ᵥ Pi.single (reflectionClean n x) 1 =
      (if x.1=(true,true) then (if x.2=(1,fun _=>false) then (1:ℂ) else -1) else 1) •
        (Pi.single (reflectionClean n x) 1 : ReflectionState n→ℂ) := by
  rw [reflectionPhaseCode,phaseEval_append,Submonoid.coe_mul,← Matrix.mulVec_mulVec]
  have hb : (false,(reflectionClean n x).2)=reflectionClean n x := rfl
  have h₁ := maskedPhaseCode_basis 2 (reflectionLabelControls n)
    (reflectionLabelControls_injective n) (fun _=>true) matchSign (reflectionClean n x).2 (by rfl)
  have h₂ := maskedPhaseCode_basis (Fintype.card (ReflectionBit n)) (reflectionPointControls n)
    (reflectionPointControls_injective n)
    (fun i=>reflectionPointMask n ((Fintype.equivFin (ReflectionBit n)).symm i))
    matchSign (reflectionClean n x).2 (by rfl)
  rw [hb] at h₁ h₂
  rw [h₁,Matrix.mulVec_smul,h₂,smul_smul]
  simp only [reflectionLabel_matches,reflectionPoint_matches]
  by_cases hm : x.1=(true,true) <;> by_cases hx : x.2=(1,fun _=>false) <;>
    simp [hm,hx,matchSign_val]

/-- Full coherent clean-subspace semantics for the literal O(n) elementary word. -/
theorem reflectionPhaseCode_intertwines (n : ℕ) :
    (phaseEval (reflectionPhaseCode n)).val*basisInsertion (reflectionClean n)=
      basisInsertion (reflectionClean n)*(reflectionPhaseUnitary n).val := by
  apply basisInsertion_intertwines
  intro x
  rw [reflectionPhaseCode_basis,reflectionPhaseUnitary_basis,Matrix.mulVec_smul,basisInsertion_basis]

end OptimalQLS.Preparation.CompilerAttachment
