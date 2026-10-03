import OptimalQLS.Preparation.CompilerAttachment.WorkConjugation
import OptimalQLS.Preparation.CompilerAttachment.WorkNaturality
import OptimalQLS.Preparation.CompilerAttachment.Frames
import OptimalQLS.PolynomialTransform.GraphKernel

/-! # Existing-cache work control in the full preparation compiler register -/
noncomputable section
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.Preparation.CompilerAttachment
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla

abbrev WorkRest (ℓ : ℕ) := Bool × (Bits (ℓ+1) × Bits ℓ)

/-- Only existing compiler wires: the control is cache0; its tail, the entire
clock, and the old compiler synthesis qubit remain spectators. -/
def workSourceFrame (a n ℓ : ℕ) :
    WorkSource (a+4) (Fin 4 × Bits n) × WorkRest ℓ ≃ Logical a n (ℓ+1) where
  toFun p :=
    (p.2.1,(((p.1.1.1.1,((graphSignalBits a).symm p.1.1.1.2.1,p.1.1.1.2.2)),p.1.1.2),
      p.2.2.1,Fin.cons p.1.2 p.2.2.2))
  invFun p :=
    ((((p.2.1.1.1,(graphSignalBits a p.2.1.1.2.1,p.2.1.1.2.2)),p.2.1.2),p.2.2.2 0),
      p.1,p.2.2.1,Fin.tail p.2.2.2)
  left_inv p := by rcases p with ⟨⟨⟨⟨b,s,d⟩,l⟩,c⟩,z,t,cs⟩; simp
  right_inv p := by rcases p with ⟨z,⟨⟨b,s,d⟩,l⟩,t,cs⟩; simp

def workFrame (a n ℓ : ℕ) :
    WorkGates.Physical (a+4) (Fin 4 × Bits n) × WorkRest ℓ ≃ Physical a n (ℓ+1) :=
  (Equiv.prodCongr (workRegisterEquiv (a+4) (Fin 4 × Bits n)).symm
    (Equiv.refl (WorkRest ℓ))).trans (scratchFrame (workSourceFrame a n ℓ))

theorem workFrame_clean (a n ℓ : ℕ) (x : WorkSource (a+4) (Fin 4 × Bits n)) (r : WorkRest ℓ) :
    workFrame a n ℓ (workInsertion false x,r)=clean a n (ℓ+1) (workSourceFrame a n ℓ (x,r)) := by
  simp only [workInsertion_registerEquiv,workFrame,Equiv.trans_apply,Equiv.prodCongr_apply,
    Equiv.symm_apply_apply]
  simp [Prod.map_apply,scratchFrame,clean]

theorem workFrame_intertwines (a n ℓ : ℕ) {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) :
    (GateSynthesis.placeHom (workFrame a n ℓ)
      (placedPhaseWord (D := Fin 4 × Bits n) (compiledWorkProgram (a+4) hμ hr true))).val *
        basisInsertion (clean a n (ℓ+1))=
      basisInsertion (clean a n (ℓ+1))*
        (GateSynthesis.placeHom (workSourceFrame a n ℓ)
          (compilerSourceWork (D := Fin 4 × Bits n) (a := a+4) hμ hr true)).val := by
  have ht := tensor_intertwines (D := WorkRest ℓ) (workInsertion false)
    (placedPhaseWord (D := Fin 4 × Bits n) (compiledWorkProgram (a+4) hμ hr true))
    (compilerSourceWork hμ hr true) (compiledWorkProgram_intertwines hμ hr true false)
  have he := clean_intertwines_transport (workFrame a n ℓ) (workSourceFrame a n ℓ)
    (fun x => (workInsertion false x.1,x.2)) _ _ ht
  have hc : (fun x => workFrame a n ℓ
      (workInsertion false ((workSourceFrame a n ℓ).symm x).1,
        ((workSourceFrame a n ℓ).symm x).2))=clean a n (ℓ+1) := by
    funext x
    rw [workFrame_clean,Equiv.apply_symm_apply]
  rw [hc] at he
  exact he

theorem workSourceFrame_compilerWork (a n ℓ : ℕ) {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) :
    GateSynthesis.placeHom (workSourceFrame a n ℓ)
      (compilerSourceWork (D := Fin 4 × Bits n) (a := a+4) hμ hr true)=
      padHom (cachedWork (compilerWork
        (signalProjector (D := Fin 4 × Bits n) (GraphEncoding.physicalSignalZero (fun _ : Fin a=>false)))
        (signalProjector_star _) (signalProjector_idempotent _) hμ hr)) := by
  rw [compilerSourceWork_eq]
  apply Subtype.ext
  ext x y
  obtain ⟨⟨⟨⟨⟨b,s,d⟩,l⟩,c⟩,z,t,cs⟩,rfl⟩ := (workSourceFrame a n ℓ).surjective x
  obtain ⟨⟨⟨⟨⟨b',s',d'⟩,l'⟩,c'⟩,z',t',cs'⟩,rfl⟩ := (workSourceFrame a n ℓ).surjective y
  rw [placeHom_entry]
  simp only [controlledOn,Matrix.blockDiagonal_apply,Bool.not_true,Bool.false_or,
    padHom,GraphEncoding.placeHom_entries,workSourceFrame,Equiv.prodComm_symm,
    Equiv.prodComm_apply,Prod.swap,cachedWork,cacheFlag,dif_pos (Nat.zero_lt_succ ℓ),
    Fin.cons_zero]
  have hzero (s : Bits (a+4)) :
      (graphSignalBits a).symm s=GraphEncoding.physicalSignalZero (fun _ : Fin a=>false) ↔
        s=(fun _=>false) := by
    rw [Equiv.symm_apply_eq,graphSignalBits_zero]
  by_cases hz : z=z' <;> by_cases ht : t=t' <;> by_cases hcs : cs=cs' <;>
    by_cases hcc : c=c' <;> by_cases hss : s=s' <;> by_cases hd : d=d' <;>
    cases c <;> cases c' <;>
    simp_all [Matrix.one_apply,Prod.mk.injEq,hzero,
      (graphSignalBits a).symm.injective.eq_iff,Fin.cons_inj]
  all_goals
    simp_all [compilerWork,rewireUnitary,preparationWork_fiber,compilerWiring,
      WorkGates.fiberMatrix,Prod.mk.injEq,hzero,(graphSignalBits a).symm.injective.eq_iff]

end OptimalQLS.Preparation.CompilerAttachment
