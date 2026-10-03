import OptimalQLS.Preparation.OriginalState

/-! # The actual computational input basis of preparation -/
noncomputable section
namespace OptimalQLS.Preparation
open Matrix TransducerCompiler BinaryClock GraphEncoding
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
variable {S D : Type*} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]

def preparationBasisIndex (s₀ : S) (i₀ : D) (ℓ : ℕ) : SynthSpace (PreparationData S D) ℓ :=
  (false,(((false,(physicalSignalZero s₀,(1,i₀))),.pub),((fun _=>false),(fun _=>false))))

theorem synthInput_single {N : Type*} [Fintype N] [DecidableEq N] {ℓ : ℕ}
    (b : Layout (2^ℓ)) (i₀ : N) :
    synthInput b (Pi.single i₀ 1)=Pi.single (false,((i₀,Label.pub),((fun _=>false),(fun _=>false)))) 1 := by
  have hz (t : Bits ℓ) : HadamardClock.bitsFinEquiv ℓ t=b.zero ↔ t=fun _=>false := by
    have he : b.zero=HadamardClock.bitsFinEquiv ℓ (fun _=>false) := by
      rw [HadamardClock.bitsFinEquiv_zero]; rfl
    rw [he,Equiv.apply_eq_iff_eq]
  ext ⟨syn,⟨i,l⟩,t,c⟩
  cases syn <;> cases l <;>
    simp [synthInput,synthClean,cachedInput,TransducerCompiler.cleanVector,inputToBits,
      inputState,spaceBitsEquiv,Pi.single_apply,hz,ite_and]
  split_ifs <;> rfl

theorem preparationInternal_single (s₀ : S) (i₀ : D) :
    preparationInternal s₀ (Pi.single i₀ 1)=Pi.single (false,(s₀,i₀)) 1 := by
  ext ⟨b,s,i⟩
  cases b <;> simp [preparationInternal,doubleVector,Matrix.mulVec_single_one,
    signalInjection,Pi.single_apply,ite_and]

theorem preparationBasisInput_single (s₀ : S) (i₀ : D) {κ s ŝ : ℝ}
    (h : BudgetParameters κ s ŝ) :
    preparationBasisInput s₀ i₀ h=Pi.single (preparationBasisIndex s₀ i₀ (preparationExponent κ)) 1 := by
  have hj : signalInjection (1 : Fin 4)*ᵥPi.single i₀ (1 : ℂ)=Pi.single (1,i₀) 1 := by
    ext ⟨g,i⟩
    simp [Matrix.mulVec_single_one,signalInjection,Pi.single_apply,ite_and]
  rw [preparationBasisInput,hj,preparationInternal_single,synthInput_single]
  rfl

end OptimalQLS.Preparation
