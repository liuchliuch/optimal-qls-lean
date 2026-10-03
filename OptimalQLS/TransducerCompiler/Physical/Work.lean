import OptimalQLS.TransducerCompiler.Physical.Basic

/-! Literal substitution of the supplied controlled-work circuit. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.TransducerCompiler.Physical
open Matrix BinaryClock PolynomialTransform

def padded (m ℓ : ℕ) (U : Matrix.unitaryGroup (SynthSpace (Bits m) ℓ) ℂ) :
    Matrix.unitaryGroup (Space m ℓ) ℂ := GateSynthesis.placeHom (Equiv.refl _) U

theorem padded_clean (m ℓ : ℕ) (U : Matrix.unitaryGroup (SynthSpace (Bits m) ℓ) ℂ) :
    (padded m ℓ U).val*basisInsertion (clean m ℓ)=basisInsertion (clean m ℓ)*U.val := by
  apply basisInsertion_intertwines
  intro i
  change (GateSynthesis.placeHom (Equiv.refl _) U).val*ᵥPi.single (i,(false,false,false)) 1=_
  have hb := placeHom_basis_sum (Equiv.refl (Space m ℓ)) U i (false,false,false)
  simp only [Equiv.refl_apply] at hb
  rw [hb]
  ext j
  simp [clean,basisInsertion,Matrix.mulVec_single_one,Matrix.col_apply,Matrix.mulVec,dotProduct,Pi.single_apply]

theorem work_placement (m ℓ : ℕ) (hℓ : 0<ℓ) (S : Matrix.unitaryGroup (Base (Bits m)) ℂ) :
    GateSynthesis.placeHom (workFrame m ℓ hℓ) ((Reduction.bitControlPort (Base (Bits m))).apply S)=
      padded m ℓ (padHom (cachedWork S)) := by
  apply Subtype.ext
  ext x y
  obtain ⟨⟨⟨b,u⟩,z,t,r,s⟩,rfl⟩ := (workFrame m ℓ hℓ).surjective x
  obtain ⟨⟨⟨c,v⟩,w,t',r',s'⟩,rfl⟩ := (workFrame m ℓ hℓ).surjective y
  rw [placeHom_entry,Reduction.bitControlPort_entries]
  have hc : ((Equiv.funSplitAt (⟨0,hℓ⟩ : Fin ℓ) Bool).symm (b,r)=
      (Equiv.funSplitAt (⟨0,hℓ⟩ : Fin ℓ) Bool).symm (c,r')) ↔ b=c ∧ r=r' := by
    rw [Equiv.apply_eq_iff_eq,Prod.mk.injEq]
  change _=(GateSynthesis.placeHom (Equiv.refl _) (padHom (cachedWork S))).val
    ((z,(u,(t,(Equiv.funSplitAt (⟨0,hℓ⟩ : Fin ℓ) Bool).symm (b,r)))),s)
    ((w,(v,(t',(Equiv.funSplitAt (⟨0,hℓ⟩ : Fin ℓ) Bool).symm (c,r')))),s')
  have hs0 := placeHom_entry (Equiv.refl (Space m ℓ)) (padHom (cachedWork (ℓ := ℓ) S))
    (z,(u,(t,(Equiv.funSplitAt (⟨0,hℓ⟩ : Fin ℓ) Bool).symm (b,r))))
    (w,(v,(t',(Equiv.funSplitAt (⟨0,hℓ⟩ : Fin ℓ) Bool).symm (c,r')))) s s'
  simp only [Equiv.refl_apply] at hs0
  rw [hs0]
  change _=if s=s' then (GateSynthesis.placeHom (Equiv.prodComm _ _) (cachedWork S)).val
    ((Equiv.prodComm _ _) ((u,(t,(Equiv.funSplitAt (⟨0,hℓ⟩ : Fin ℓ) Bool).symm (b,r))),z))
    ((Equiv.prodComm _ _) ((v,(t',(Equiv.funSplitAt (⟨0,hℓ⟩ : Fin ℓ) Bool).symm (c,r'))),w)) else 0
  rw [placeHom_entry (Equiv.prodComm _ _) (cachedWork (ℓ := ℓ) S)]
  simp only [cachedWork,controlledOn,Matrix.blockDiagonal_apply,cacheFlag,dif_pos hℓ,
    Equiv.funSplitAt_symm_apply,if_pos rfl,Matrix.one_apply,Prod.mk.injEq,hc]
  by_cases hz : z=w <;> by_cases ht : t=t' <;> by_cases hr : r=r' <;>
    by_cases hs : s=s' <;> by_cases hb : b=c <;> simp_all
  cases c <;> simp [Matrix.one_apply]

def workGateEval (m ℓ : ℕ) (hℓ : 0<ℓ) (g : LocalGate (workCoordinates m)) :
    Matrix.unitaryGroup (Space m ℓ) ℂ := GateSynthesis.placeHom (workFrame m ℓ hℓ) g.eval

def workCode (m ℓ : ℕ) (c : WorkCircuit m) :
    NamedCircuit (LocalGate (workCoordinates m)) (Bits m) (Bits m) (Space m ℓ) := c.map .gate

theorem workCode_counts (m ℓ : ℕ) (hℓ : 0<ℓ) (c : WorkCircuit m) :
    ((workCode m ℓ c).toQuery (workGateEval m ℓ hℓ)).matrixQueries=0 ∧
    ((workCode m ℓ c).toQuery (workGateEval m ℓ hℓ)).vectorQueries=0 ∧
    (workCode m ℓ c).workGates=c.length := by
  induction c with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons g c ih => exact ⟨ih.1,ih.2.1,congrArg Nat.succ ih.2.2⟩

theorem workCode_eval (m ℓ : ℕ) (hℓ : 0<ℓ) (c : WorkCircuit m)
    (U₁ U₂ : Matrix.unitaryGroup (Bits m) ℂ) :
    ((workCode m ℓ c).toQuery (workGateEval m ℓ hℓ)).eval U₁ U₂=
      GateSynthesis.placeHom (workFrame m ℓ hℓ) (localEval c) := by
  induction c with
  | nil => simp [workCode,NamedCircuit.toQuery,QueryCircuit.eval,localEval]
  | cons g c ih =>
    simp only [workCode,List.map_cons,NamedCircuit.toQuery,NamedInstruction.toQuery,
      QueryCircuit.eval,QueryInstruction.eval,localEval,map_mul]
    exact congrArg (fun U=>U*workGateEval m ℓ hℓ g) ih

theorem workCode_intertwines (m ℓ : ℕ) (hℓ : 0<ℓ) (S : Matrix.unitaryGroup (Base (Bits m)) ℂ)
    (c : WorkCircuit m) (hc : ControlledWork S c) (U₁ U₂ : Matrix.unitaryGroup (Bits m) ℂ) :
    (((workCode m ℓ c).toQuery (workGateEval m ℓ hℓ)).eval U₁ U₂).val*basisInsertion (clean m ℓ)=
      basisInsertion (clean m ℓ)*((SynthInstruction.work).eval S U₁ U₂).val := by
  rw [workCode_eval,hc,work_placement,padded_clean]
  rfl

end OptimalQLS.TransducerCompiler.Physical
