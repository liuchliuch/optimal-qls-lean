import OptimalQLS.Preparation.CompilerAttachment.Frames
import OptimalQLS.Preparation.CompilerAttachment.ReflectionPhase
import OptimalQLS.Preparation.CompilerAttachment.LocalOracle

/-! # Literal source-oracle and basis-reflection wire regroupings -/
noncomputable section
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.Preparation.CompilerAttachment
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla

abbrev SourceRest (a ℓ : ℕ) := GraphEncoding.PhysicalSignal (Bits a) × (Fin 4 × CompilerRest ℓ)
abbrev ReflectionRest (a ℓ : ℕ) := GraphEncoding.PhysicalSignal (Bits a) × CompilerRest ℓ

def sourceDataFrame (a n ℓ : ℕ) :
    (((Bool × Bool) × Bits n) × SourceRest a ℓ) ≃ Logical a n ℓ where
  toFun p := labelDataFrame a n ℓ ((p.1.1,(p.2.1,(p.2.2.1,p.1.2))),p.2.2.2)
  invFun p :=
    let x := (labelDataFrame a n ℓ).symm p
    ((x.1.1,x.1.2.2.2),(x.1.2.1,x.1.2.2.1,x.2))
  left_inv p := by rcases p with ⟨⟨m,d⟩,s,g,r⟩; simp
  right_inv p := by simp

def vectorFrame (a n ℓ : ℕ) :
    (OracleLocalState × Bits n) × SourceRest a ℓ ≃ Physical a n ℓ :=
  (Equiv.prodCongr (oracleLocalWiring (Bits n)) (Equiv.refl (SourceRest a ℓ))).trans
    (scratchFrame (sourceDataFrame a n ℓ))

theorem vectorFrame_clean (a n ℓ : ℕ) (x : (Bool × Bool) × Bits n) (r : SourceRest a ℓ) :
    vectorFrame a n ℓ (oracleLocalClean x,r)=clean a n ℓ (sourceDataFrame a n ℓ (x,r)) := by
  simp [vectorFrame,oracleLocalClean,scratchFrame,clean]

def reflectionSourceFrame (a n ℓ : ℕ) :
    ReflectionSource n × ReflectionRest a ℓ ≃ Logical a n ℓ where
  toFun p := labelDataFrame a n ℓ ((p.1.1,(p.2.1,p.1.2)),p.2.2)
  invFun p :=
    let x := (labelDataFrame a n ℓ).symm p
    ((x.1.1,x.1.2.2),(x.1.2.1,x.2))
  left_inv p := by rcases p with ⟨⟨m,x⟩,s,r⟩; simp
  right_inv p := by simp

def reflectionFrame (a n ℓ : ℕ) :
    ReflectionState n × ReflectionRest a ℓ ≃ Physical a n ℓ :=
  (Equiv.prodCongr (reflectionRegister n).symm (Equiv.refl (ReflectionRest a ℓ))).trans
    (scratchFrame (reflectionSourceFrame a n ℓ))

theorem reflectionFrame_clean (a n ℓ : ℕ) (x : ReflectionSource n) (r : ReflectionRest a ℓ) :
    reflectionFrame a n ℓ (reflectionClean n x,r)=clean a n ℓ (reflectionSourceFrame a n ℓ (x,r)) := by
  simp [reflectionFrame,reflectionClean,scratchFrame,clean]

theorem vectorFrame_intertwines (a n ℓ : ℕ)
    (U : Matrix.unitaryGroup (OracleLocalState × Bits n) ℂ)
    (V : Matrix.unitaryGroup ((Bool × Bool) × Bits n) ℂ)
    (h : U.val*basisInsertion oracleLocalClean=basisInsertion oracleLocalClean*V.val) :
    (GateSynthesis.placeHom (vectorFrame a n ℓ) U).val*basisInsertion (clean a n ℓ)=
      basisInsertion (clean a n ℓ)*(GateSynthesis.placeHom (sourceDataFrame a n ℓ) V).val := by
  have ht := tensor_intertwines (D := SourceRest a ℓ) oracleLocalClean U V h
  have he := clean_intertwines_transport (vectorFrame a n ℓ) (sourceDataFrame a n ℓ)
    (fun x => (oracleLocalClean x.1,x.2)) _ _ ht
  have hc : (fun x => vectorFrame a n ℓ
      (oracleLocalClean ((sourceDataFrame a n ℓ).symm x).1,((sourceDataFrame a n ℓ).symm x).2))=
      clean a n ℓ := by
    funext x
    rw [vectorFrame_clean,Equiv.apply_symm_apply]
  rw [hc] at he
  exact he

theorem reflectionFrame_intertwines (a n ℓ : ℕ) :
    (GateSynthesis.placeHom (reflectionFrame a n ℓ) (phaseEval (reflectionPhaseCode n))).val *
        basisInsertion (clean a n ℓ)=
      basisInsertion (clean a n ℓ)*
        (GateSynthesis.placeHom (reflectionSourceFrame a n ℓ) (reflectionPhaseUnitary n)).val := by
  have ht := tensor_intertwines (D := ReflectionRest a ℓ) (reflectionClean n)
    (phaseEval (reflectionPhaseCode n)) (reflectionPhaseUnitary n) (reflectionPhaseCode_intertwines n)
  have he := clean_intertwines_transport (reflectionFrame a n ℓ) (reflectionSourceFrame a n ℓ)
    (fun x => (reflectionClean n x.1,x.2)) _ _ ht
  have hc : (fun x => reflectionFrame a n ℓ
      (reflectionClean n ((reflectionSourceFrame a n ℓ).symm x).1,
        ((reflectionSourceFrame a n ℓ).symm x).2))=clean a n ℓ := by
    funext x
    rw [reflectionFrame_clean,Equiv.apply_symm_apply]
  rw [hc] at he
  exact he

end OptimalQLS.Preparation.CompilerAttachment
