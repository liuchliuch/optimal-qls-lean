import OptimalQLS.TransducerCompiler.Physical.Auxiliary
import OptimalQLS.Preparation.CompilerAttachment.LocalAttach

/-! The two old label bits and the actual oracle data register, with fixed spectators. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.TransducerCompiler.Physical
open Matrix BinaryClock PolynomialTransform DirtyAncilla
open Preparation.CompilerAttachment (scratchFrame)

abbrev QueryRest (ℓ : ℕ) := Bool × (Bits ℓ × Bits ℓ)

def labelFrame (m ℓ : ℕ) : (((Bool × Bool) × Bits m) × QueryRest ℓ) ≃ SynthSpace (Bits m) ℓ where
  toFun p := (p.2.1,((p.1.2,labelBitsEquiv.symm p.1.1),p.2.2))
  invFun p := (((labelBitsEquiv p.2.1.2),p.2.1.1),p.1,p.2.2)
  left_inv p := by rcases p with ⟨⟨b,d⟩,z,t,c⟩; simp
  right_inv p := by rcases p with ⟨z,⟨d,l⟩,t,c⟩; simp

def queryFrame (m ℓ : ℕ) : ((OracleLocalState × Bits m) × QueryRest ℓ) ≃ Space m ℓ :=
  (Equiv.prodCongr (oracleLocalWiring (Bits m)) (Equiv.refl _)).trans (scratchFrame (labelFrame m ℓ))

theorem queryFrame_clean (m ℓ : ℕ) (x : (Bool × Bool) × Bits m) (r : QueryRest ℓ) :
    queryFrame m ℓ (oracleLocalClean x,r)=clean m ℓ (labelFrame m ℓ (x,r)) := by
  simp [queryFrame,oracleLocalClean,scratchFrame,clean]

/-- The logical masked port is exactly the compiler's label-controlled oracle,
on every column, including all nonpublic labels and arbitrary clock/cache bits. -/
theorem label_query_eq (m ℓ : ℕ) (l : Label) (U : Matrix.unitaryGroup (Bits m) ℂ) :
    GateSynthesis.placeHom (labelFrame m ℓ)
      ((GraphEncoding.maskedGraphPort (Bits m) (labelBitsEquiv l)).apply U)=
      padHom (dataQuery (a := Bits ℓ × Bits ℓ) l U) := by
  apply Subtype.ext
  ext x y
  obtain ⟨⟨⟨b,u⟩,z,t,c⟩,rfl⟩ := (labelFrame m ℓ).surjective x
  obtain ⟨⟨⟨b',v⟩,w,t',c'⟩,rfl⟩ := (labelFrame m ℓ).surjective y
  rw [placeHom_entry,GraphEncoding.maskedGraphPort_apply_entries]
  have hl : labelBitsEquiv.symm b=l ↔ b=labelBitsEquiv l := by
    rw [Equiv.symm_apply_eq]
  have hb : labelBitsEquiv.symm b=labelBitsEquiv.symm b' ↔ b=b' :=
    labelBitsEquiv.symm.injective.eq_iff
  change _=(GateSynthesis.placeHom (Equiv.prodComm _ _) (dataQuery l U)).val
    ((Equiv.prodComm _ _) (((u,labelBitsEquiv.symm b),(t,c)),z))
    ((Equiv.prodComm _ _) (((v,labelBitsEquiv.symm b'),(t',c')),w))
  rw [placeHom_entry (Equiv.prodComm _ _) (dataQuery l U)]
  simp only [dataQuery,rewireUnitary,Matrix.submatrix_apply,Equiv.prodAssoc_apply,
    controlledOn,Matrix.blockDiagonal_apply,Prod.mk.injEq,hl,hb,decide_eq_true_eq]
  by_cases hz : z=w <;> by_cases ht : t=t' <;> by_cases hc : c=c' <;>
    by_cases hb' : b=b' <;> simp_all
  split_ifs <;> simp_all [Matrix.one_apply]

end OptimalQLS.TransducerCompiler.Physical
