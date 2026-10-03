import OptimalQLS.TransducerCompiler.Physical.Resources
import OptimalQLS.Preparation.BasisInput

/-! The public input is the original data with every auxiliary bit literally zero. -/
noncomputable section
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.TransducerCompiler.Physical
open Matrix BinaryClock PolynomialTransform

def publicIndex (m ℓ : ℕ) (i : Bits m) : Space m ℓ :=
  clean m ℓ (false,((i,.pub),((fun _=>false),(fun _=>false))))

def publicInput (m ℓ : ℕ) (ξ : Bits m → ℂ) : Space m ℓ → ℂ :=
  basisInsertion (publicIndex m ℓ)*ᵥξ

theorem synthInput_entries (m ℓ : ℕ) (b : Layout (2^ℓ)) (ξ : Bits m → ℂ)
    (x : SynthSpace (Bits m) ℓ) :
    synthInput b ξ x =
      if x.1=false ∧ x.2.1.2=.pub ∧ x.2.2.1=(fun _=>false) ∧ x.2.2.2=(fun _=>false)
      then ξ x.2.1.1 else 0 := by
  have hz (t : Bits ℓ) : HadamardClock.bitsFinEquiv ℓ t=b.zero ↔ t=fun _=>false := by
    have he : b.zero=HadamardClock.bitsFinEquiv ℓ (fun _=>false) := by
      rw [HadamardClock.bitsFinEquiv_zero]; rfl
    rw [he,Equiv.apply_eq_iff_eq]
  rcases x with ⟨syn,⟨i,l⟩,t,c⟩
  cases syn <;> cases l <;>
    simp [synthInput,synthClean,cachedInput,TransducerCompiler.cleanVector,inputToBits,
      inputState,spaceBitsEquiv,hz,ite_and]
  split_ifs <;> rfl

theorem cleanVector_entry (m ℓ : ℕ) (v : SynthSpace (Bits m) ℓ → ℂ)
    (x : SynthSpace (Bits m) ℓ) (s : PhaseScratch) :
    cleanVector m ℓ v (x,s)=if s=(false,false,false) then v x else 0 := by
  let f : SynthSpace (Bits m) ℓ ↪ Space m ℓ := ⟨clean m ℓ,fun _ _ he=>congrArg Prod.fst he⟩
  by_cases hs:s=(false,false,false)
  · subst s
    exact PhysicalPadding.insertion_mulVec_active f v x
  · rw [if_neg hs]
    apply PhysicalPadding.insertion_mulVec_inactive f v
    rintro ⟨y,hy⟩
    exact hs (congrArg Prod.snd hy).symm

theorem publicInput_eq (m ℓ : ℕ) (b : Layout (2^ℓ)) (ξ : Bits m → ℂ) :
    publicInput m ℓ ξ=cleanVector m ℓ (synthInput b ξ) := by
  ext ⟨x,s⟩
  rw [cleanVector_entry,synthInput_entries]
  rcases x with ⟨syn,⟨i,l⟩,t,c⟩
  unfold publicInput
  simp only [Matrix.mulVec,dotProduct,basisInsertion,publicIndex,clean,Prod.mk.injEq,
    ite_mul,one_mul,zero_mul]
  cases syn <;> cases l <;> simp [eq_comm,ite_and]
  split_ifs <;> rfl

/-- Full auxiliary-zero state in the literal physical bit chart. -/
theorem publicIndex_coordinates (m ℓ : ℕ) (i : Bits m) (j : Wire m ℓ) :
    coordinates m ℓ (publicIndex m ℓ i) j=
      match j with | .inl (.inr (.inl (.inl k))) => i k | _ => false := by
  rcases j with (j|((j|j)|j))|j
  · rfl
  · rfl
  · rcases j with j|j <;> rfl
  · rcases j with j|j <;> rfl
  · rcases j with j|(j|j) <;> rfl

end OptimalQLS.TransducerCompiler.Physical
