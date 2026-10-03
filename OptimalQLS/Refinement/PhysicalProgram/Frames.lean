import OptimalQLS.Preparation.CompilerAttachment.Complete
import OptimalQLS.Refinement.NamedProgram
import OptimalQLS.Refinement.RunCorrectness

/-! # Literal disjoint physical registers for one complete QLS run -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.Refinement.PhysicalProgram
open Matrix TransducerCompiler BinaryClock PolynomialTransform

abbrev PrepAux (a ℓ : ℕ) := CoarseAux (GraphEncoding.PhysicalSignal (Bits a)) ℓ × PhaseScratch
abbrev Register (a n ℓ : ℕ) := RunSpace a (PrepAux a ℓ) (Bits n)

def preparationCoordinates (a n ℓ : ℕ) : Preparation.CompilerAttachment.Physical a n ℓ ≃ PrepAux a ℓ × (Fin 4 × Bits n) where
  toFun p :=
    let x := (coarseWiring (GraphEncoding.PhysicalSignal (Bits a)) (Bits n) ℓ).symm p.1
    ((x.1,p.2),x.2)
  invFun p := (coarseWiring (GraphEncoding.PhysicalSignal (Bits a)) (Bits n) ℓ (p.1.1,p.2),p.1.2)
  left_inv p := by rcases p with ⟨x,s⟩; simp
  right_inv p := by rcases p with ⟨⟨x,s⟩,d⟩; simp

def preparationFrame (a n ℓ : ℕ) :
    Preparation.CompilerAttachment.Physical a n ℓ × (CorrectionSignal a × FilterSignal a) ≃ Register a n ℓ :=
  (Equiv.prodCongr (preparationCoordinates a n ℓ) (Equiv.refl _)).trans
    (preparationRunWiring (PrepAux a ℓ) (FilterSignal a) (CorrectionSignal a) (Bits n))

def preparationPort (a n ℓ : ℕ) : QueryPort (Preparation.CompilerAttachment.Physical a n ℓ) (Register a n ℓ) :=
  scratchPort (preparationFrame a n ℓ)

def prepZero (a ℓ : ℕ) : PrepAux a ℓ :=
  (coarseZero (GraphEncoding.physicalSignalZero (fun _ : Fin a=>false)) ℓ,(false,false,false))

def initial (a n ℓ : ℕ) : Register a n ℓ :=
  preparationFrame a n ℓ (Preparation.CompilerAttachment.allZero a n ℓ,(physicalZero a,physicalZero (a+4)))

def coarseVector (a n ℓ : ℕ) (v : Preparation.CompilerAttachment.Logical a n ℓ→ℂ) : PrepAux a ℓ × (Fin 4 × Bits n)→ℂ :=
  (basisInsertion (Preparation.CompilerAttachment.clean a n ℓ)*ᵥv) ∘ (preparationCoordinates a n ℓ).symm

/-- The three new preparation scratch bits are included in the single accepting zero test. -/
theorem coarseVector_slice (a n ℓ : ℕ) (v : Preparation.CompilerAttachment.Logical a n ℓ→ℂ) :
    (fun x=>coarseVector a n ℓ v (prepZero a ℓ,x))=
      Alignment.zeroAuxiliaryOutput (GraphEncoding.physicalSignalZero (fun _ : Fin a=>false)) v := by
  funext x
  change (basisInsertion (Preparation.CompilerAttachment.clean a n ℓ)*ᵥv)
    (coarseWiring (GraphEncoding.PhysicalSignal (Bits a)) (Bits n) ℓ
      (coarseZero (GraphEncoding.physicalSignalZero (fun _ : Fin a=>false)) ℓ,x),(false,false,false))=_
  rw [Preparation.CompilerAttachment.cleanVector_apply]
  rfl

theorem preparationPort_relabel (a n ℓ : ℕ) (U : Matrix.unitaryGroup (Preparation.CompilerAttachment.Physical a n ℓ) ℂ) :
    (preparationPort a n ℓ).apply U=
      (preparationRunPort (PrepAux a ℓ) (FilterSignal a) (CorrectionSignal a) (Bits n)).apply
        (rewireUnitary (preparationCoordinates a n ℓ) U) := by
  symm
  exact scratchPort_relabel _ _ U

/-- The complete workspace cardinality is derived from actual product registers. -/
theorem register_card (a n ℓ : ℕ) : Fintype.card (Register a n ℓ)=2^(n+3*a+2*ℓ+27) := by
  have he := Fintype.card_congr (preparationFrame a n ℓ)
  rw [Fintype.card_prod,Preparation.CompilerAttachment.physical_card] at he
  have hf := physical_signal_cardinality (a+4)
  have hc := physical_signal_cardinality a
  change Fintype.card (FilterSignal a)=2^(a+9) at hf
  change Fintype.card (CorrectionSignal a)=2^(a+5) at hc
  rw [Fintype.card_prod,hc,hf,←pow_add,←pow_add] at he
  rw [←he]
  congr 1
  omega

end OptimalQLS.Refinement.PhysicalProgram
