import OptimalQLS.Reduction.CircuitBridges
import OptimalQLS.Refinement.PhysicalProgram.Reparameterize
import OptimalQLS.OracleCoordinates

/-! Literal extraction of an existing single control wire; no predicate computation. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.Reduction.PhysicalAdapter
open Matrix PolynomialTransform TransducerCompiler BinaryClock
variable {A Q P : Type} [Fintype A] [DecidableEq A]
  [Fintype Q] [DecidableEq Q] [Fintype P] [DecidableEq P]

structure ControlFrame (p : QueryPort A P) where
  Rest : Type
  [finiteRest : Fintype Rest]
  [decidableRest : DecidableEq Rest]
  wiring : (Bool × A) × Rest ≃ P
  correct : ∀ U : Matrix.unitaryGroup A ℂ,
    p.apply U=GateSynthesis.placeHom wiring ((bitControlPort A).apply U)
attribute [instance] ControlFrame.finiteRest ControlFrame.decidableRest

def flagFrame {ι : Type} [Fintype ι] [DecidableEq ι] (t : ι) (A : Type) :
    (Bool × A) × (Bool × ({i : ι // i≠t} → Bool)) ≃ GateSynthesis.Space ι × A where
  toFun p := ((p.2.1,(Equiv.funSplitAt t Bool).symm (p.1.1,p.2.2)),p.1.2)
  invFun p := ((p.1.2 t,p.2),(p.1.1,fun i=>p.1.2 i))
  left_inv p := by
    rcases p with ⟨⟨b,a⟩,z,r⟩
    simp only [Equiv.funSplitAt,Equiv.piSplitAt,Equiv.coe_fn_symm_mk, dite_true]
    congr 2
    funext i
    simp [i.property]
  right_inv p := by
    rcases p with ⟨⟨z,b⟩,a⟩
    change ((z,(Equiv.funSplitAt t Bool).symm ((Equiv.funSplitAt t Bool) b)),a)=((z,b),a)
    rw [Equiv.symm_apply_apply]

def singleFlagFrame {ι : Type} [Fintype ι] [DecidableEq ι] (t : ι) :
    ControlFrame (GraphEncoding.singleFlagOraclePort A t) where
  Rest := Bool × ({i : ι // i≠t} → Bool)
  wiring := flagFrame t A
  correct U := by
    apply Subtype.ext
    ext x y
    obtain ⟨⟨⟨b,i⟩,z,r⟩,rfl⟩ := (flagFrame t A).surjective x
    obtain ⟨⟨⟨c,j⟩,w,s⟩,rfl⟩ := (flagFrame t A).surjective y
    rw [placeHom_entry,bitControlPort_entries]
    simp only [flagFrame,Equiv.coe_fn_mk,GraphEncoding.singleFlagOracle_entries]
    have he : ((Equiv.funSplitAt t Bool).symm (b,r) =
        (Equiv.funSplitAt t Bool).symm (c,s)) ↔ b=c ∧ r=s := by
      rw [Equiv.apply_eq_iff_eq,Prod.mk.injEq]
    simp only [Equiv.funSplitAt_symm_apply,if_pos rfl]
    by_cases hz : z=w <;> by_cases hb : b=c <;> by_cases hr : r=s <;>
      simp_all [Prod.mk.injEq,he]

def ControlFrame.lift {q : QueryPort A Q} (F : ControlFrame q)
    (p : QueryPort Q P) (hp : ∀ k,p.control k=true) : ControlFrame (p.comp q) where
  Rest := F.Rest × Fin p.multiplicity
  wiring := (Equiv.prodAssoc (Bool × A) F.Rest (Fin p.multiplicity)).symm.trans
    ((Equiv.prodCongr F.wiring (Equiv.refl _)).trans p.wiring)
  correct U := by
    rw [QueryPort.comp_apply,F.correct]
    apply Subtype.ext
    ext x y
    obtain ⟨⟨i,k⟩,rfl⟩ := p.wiring.surjective x
    obtain ⟨⟨j,l⟩,rfl⟩ := p.wiring.surjective y
    obtain ⟨⟨u,r⟩,rfl⟩ := F.wiring.surjective i
    obtain ⟨⟨v,s⟩,rfl⟩ := F.wiring.surjective j
    rw [QueryPort.apply_entries,hp]
    simp only [ite_true,placeHom_entry]
    have he := placeHom_entry
      ((Equiv.prodAssoc (Bool × A) F.Rest (Fin p.multiplicity)).symm.trans
        ((Equiv.prodCongr F.wiring (Equiv.refl _)).trans p.wiring))
      ((bitControlPort A).apply U) u v (r,k) (s,l)
    simp only [Equiv.trans_apply,Equiv.prodAssoc_symm_apply,Equiv.prodCongr_apply,
      Equiv.refl_apply,Prod.map_apply] at he
    rw [he]
    by_cases hr : r=s <;> by_cases hk : k=l <;> simp [hr,hk]

/-- Source relabeling changes the target coordinates, preserving the existing flag. -/
def ControlFrame.coordinates {q : QueryPort A P} (F : ControlFrame q)
    (e : A ≃ Q) : ControlFrame (OracleCoordinates.port e q) where
  Rest := F.Rest
  wiring := (Equiv.prodCongr (Equiv.prodCongr (Equiv.refl Bool) e.symm)
    (Equiv.refl F.Rest)).trans F.wiring
  correct U := by
    rw [OracleCoordinates.port_apply,F.correct]
    apply Subtype.ext
    ext x y
    obtain ⟨⟨⟨b,i⟩,r⟩,rfl⟩ := F.wiring.surjective x
    obtain ⟨⟨⟨c,j⟩,s⟩,rfl⟩ := F.wiring.surjective y
    rw [placeHom_entry,bitControlPort_entries]
    have he := placeHom_entry
      ((Equiv.prodCongr (Equiv.prodCongr (Equiv.refl Bool) e.symm)
        (Equiv.refl F.Rest)).trans F.wiring)
      ((bitControlPort Q).apply U) (b,e i) (c,e j) r s
    simp only [Equiv.trans_apply,Equiv.prodCongr_apply,Equiv.refl_apply,
      Equiv.symm_apply_apply,Prod.map_apply] at he
    rw [he,bitControlPort_entries]
    simp [rewireUnitary,e.injective.eq_iff]

/-- The leading physical data qubit is the dilation label. -/
def headTail (n : ℕ) : Bits (n+1) ≃ Bool × Bits n where
  toFun x := (x 0,fun i=>x i.succ)
  invFun x := Fin.cases x.1 x.2
  left_inv x := by funext i; refine Fin.cases ?_ (fun i=>?_) i <;> rfl
  right_inv x := by rcases x with ⟨b,x⟩; rfl

def sumBits (n : ℕ) : Bits (n+1) ≃ Bits n ⊕ Bits n :=
  (headTail n).trans (GraphEncoding.sumBitWiring (Bits n))

@[simp] theorem sumBits_zero (n : ℕ) : sumBits n (fun _=>false)=Sum.inl (fun _=>false) := rfl

end OptimalQLS.Reduction.PhysicalAdapter
