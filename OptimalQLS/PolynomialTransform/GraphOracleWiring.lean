import OptimalQLS.PolynomialTransform.GraphKernel
import OptimalQLS.PolynomialTransform.RegisterControls
import OptimalQLS.GraphEncoding.AllowedCalls

/-! # Canonical physical placement of the two-mask controlled graph oracle -/
noncomputable section
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000
namespace OptimalQLS.PolynomialTransform
open Matrix
variable {S D T K L P : Type*} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]
  [Fintype T] [DecidableEq T] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P]

theorem scratchPort_relabel (e : L × T ≃ P) (f : K ≃ L) (U : Matrix.unitaryGroup K ℂ) :
    (scratchPort e).apply (rewireUnitary f U)=
      (scratchPort ((Equiv.prodCongr f (Equiv.refl T)).trans e)).apply U := by
  apply Subtype.ext
  ext i j
  simp [scratchPort,QueryPort.apply,rewireUnitary,controlledUnitary,Matrix.blockDiagonal]

/-- Regrouping only the named averaging/dilation labels and binary signal coordinates. -/
def maskSignalEquiv (a : ℕ) (e : S ≃ (Fin a → Bool)) :
    (Bool × Bool) × (S × D) ≃ LogicalSignal a × D where
  toFun x := ((x.1,e x.2.1),x.2.2)
  invFun x := (x.1.1,e.symm x.1.2,x.2)
  left_inv x := by rcases x with ⟨m,s,d⟩; simp
  right_inv x := by rcases x with ⟨⟨m,s⟩,d⟩; simp

theorem nested_mask_relabel (a : ℕ) (e : S ≃ (Fin a → Bool)) (branch sector : Bool)
    (U : Matrix.unitaryGroup (S × D) ℂ) :
    rewireUnitary (twoLabelSignalEquiv (Fin a → Bool) D)
      (if branch then
        sumUnitary 1 (if sector then sumUnitary 1 (rewireUnitary (Equiv.prodCongr e (Equiv.refl D)) U)
          else sumUnitary (rewireUnitary (Equiv.prodCongr e (Equiv.refl D)) U) 1)
      else
        sumUnitary (if sector then sumUnitary 1 (rewireUnitary (Equiv.prodCongr e (Equiv.refl D)) U)
          else sumUnitary (rewireUnitary (Equiv.prodCongr e (Equiv.refl D)) U) 1) 1)=
      rewireUnitary (maskSignalEquiv a e)
        ((GraphEncoding.maskedGraphPort (S × D) (branch,sector)).apply U) := by
  apply Subtype.ext
  ext ⟨⟨⟨b,c⟩,x⟩,i⟩ ⟨⟨⟨d,f⟩,y⟩,j⟩
  change _ = ((GraphEncoding.maskedGraphPort (S × D) (branch,sector)).apply U).val
    ((b,c),e.symm x,i) ((d,f),e.symm y,j)
  rw [GraphEncoding.maskedGraphPort_apply_entries]
  cases branch <;> cases sector <;> cases b <;> cases c <;> cases d <;> cases f <;>
    simp [rewireUnitary,twoLabelSignalEquiv,sumUnitary,Matrix.one_apply,Prod.mk.injEq,e.symm.injective.eq_iff]

/-- The common workspace keeps graph data labels as data and exposes exactly
three reusable scratch bits outside the masked physical graph oracle. -/
def maskedPhysicalWiring (a : ℕ) (e : S ≃ (Fin a → Bool)) :
    ((Bool × Bool) × (S × D)) × PhaseScratch ≃ PhysicalSignal a × D :=
  (Equiv.prodCongr (maskSignalEquiv a e) (Equiv.refl PhaseScratch)).trans (physicalEquiv a D)

theorem physicalMaskedOracle_eq_graphMask (a : ℕ) (e : S ≃ (Fin a → Bool)) (branch sector : Bool)
    (U : Matrix.unitaryGroup (S × D) ℂ) :
    physicalMaskedOracle a branch sector (rewireUnitary (Equiv.prodCongr e (Equiv.refl D)) U)=
      (scratchPort (maskedPhysicalWiring a e)).apply
        ((GraphEncoding.maskedGraphPort (S × D) (branch,sector)).apply U) := by
  rw [physicalMaskedOracle,nested_mask_relabel,scratchPort_relabel]
  rfl

end OptimalQLS.PolynomialTransform
