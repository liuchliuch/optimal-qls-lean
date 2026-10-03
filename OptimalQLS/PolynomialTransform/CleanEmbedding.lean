import OptimalQLS.PolynomialTransform.QueryEncoding
import OptimalQLS.PolynomialTransform.DirtyAncilla.ControlledPhase

/-! # Clean computational embeddings and exact circuit refinement -/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Matrix
variable {L P T : Type*} [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P]
  [Fintype T] [DecidableEq T]

/-- Literal injection of computational basis labels. -/
def basisInsertion (f : L → P) : Matrix P L ℂ := fun i j => if i=f j then 1 else 0

@[simp] theorem basisInsertion_basis (f : L → P) (j : L) :
    basisInsertion f *ᵥ Pi.single j 1 = Pi.single (f j) 1 := by
  ext i
  simp [basisInsertion,Matrix.mulVec_single_one,Pi.single_apply]

theorem basisInsertion_isometry (f : L → P) (hf : Function.Injective f) :
    (basisInsertion f)ᴴ*basisInsertion f=1 := by
  ext i j
  simp [basisInsertion,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply,hf.eq_iff,eq_comm]

theorem basisInsertion_intertwines (f : L → P) (U : Matrix P P ℂ) (V : Matrix L L ℂ)
    (h : ∀ j, U *ᵥ Pi.single (f j) 1=basisInsertion f *ᵥ (V *ᵥ Pi.single j 1)) :
    U*basisInsertion f=basisInsertion f*V := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,basisInsertion_basis]
  exact h j

/-- An arbitrary work oracle is tensored with an untouched finite scratch register. -/
def scratchPort (e : L × T ≃ P) : QueryPort L P where
  multiplicity := Fintype.card T
  wiring := (Equiv.prodCongr (Equiv.refl L) (Fintype.equivFin T).symm).trans e
  control := fun _ => true

theorem scratchPort_apply (e : L × T ≃ P) (U : Matrix.unitaryGroup L ℂ) :
    (scratchPort e).apply U=TransducerCompiler.GateSynthesis.placeHom e U := by
  apply Subtype.ext
  change ((scratchPort e).apply U).val =
    (rewireUnitary e (TransducerCompiler.controlledOn (fun _ : T => true) U)).val
  ext i j
  simp [scratchPort,QueryPort.apply,rewireUnitary,controlledUnitary,
    TransducerCompiler.controlledOn,Matrix.blockDiagonal]

theorem placeHom_entry (e : L × T ≃ P) (U : Matrix.unitaryGroup L ℂ) (x y : L) (s t : T) :
    (TransducerCompiler.GateSynthesis.placeHom e U).val (e (x,s)) (e (y,t))=
      if s=t then U.val x y else 0 := by
  change (rewireUnitary e (TransducerCompiler.controlledOn (fun _ : T => true) U)).val
    (e (x,s)) (e (y,t))=_
  simp [rewireUnitary,TransducerCompiler.controlledOn,Matrix.blockDiagonal]

/-- Tensor placement preserves a proved scalar basis-vector action. -/
theorem placeHom_basis_smul (e : L × T ≃ P) (U : Matrix.unitaryGroup L ℂ)
    (i j : L) (t : T) (c : ℂ)
    (hU : U.val *ᵥ Pi.single i 1=c • (Pi.single j 1 : L → ℂ)) :
    (TransducerCompiler.GateSynthesis.placeHom e U).val *ᵥ Pi.single (e (i,t)) 1=
      c • (Pi.single (e (j,t)) 1 : P → ℂ) := by
  ext p
  obtain ⟨⟨k,s⟩,rfl⟩ := e.surjective p
  have h := congrFun hU k
  simp only [Matrix.mulVec_single_one,Matrix.col_apply,Pi.smul_apply,smul_eq_mul,
    Pi.single_apply] at h ⊢
  rw [placeHom_entry]
  by_cases hs : s=t
  · subst s
    simpa [e.injective.eq_iff] using h
  · simp [hs,e.injective.eq_iff]

/-- Exact tensor action on a computational basis column. -/
theorem placeHom_basis_sum (e : L × T ≃ P) (U : Matrix.unitaryGroup L ℂ)
    (i : L) (t : T) :
    (TransducerCompiler.GateSynthesis.placeHom e U).val *ᵥ Pi.single (e (i,t)) 1=
      ∑ j : L, U.val j i • (Pi.single (e (j,t)) 1 : P → ℂ) := by
  ext p
  obtain ⟨⟨k,s⟩,rfl⟩ := e.surjective p
  simp only [Matrix.mulVec_single_one,Matrix.col_apply,placeHom_entry]
  by_cases hs : s=t
  · subst s
    simp [Pi.single_apply,e.injective.eq_iff]
  · simp [Pi.single_apply,e.injective.eq_iff,hs]

/-- A physical tensor placement commutes with inserting untouched scratch. -/
theorem placeHom_natural {K R : Type*} [Fintype K] [DecidableEq K] [Fintype R] [DecidableEq R]
    (e₁ : K × T ≃ L) (e₂ : K × R ≃ P) (f : L → P) (g : T → R)
    (hf : ∀ k t, f (e₁ (k,t))=e₂ (k,g t)) (U : Matrix.unitaryGroup K ℂ) :
    (TransducerCompiler.GateSynthesis.placeHom e₂ U).val*basisInsertion f=
      basisInsertion f*(TransducerCompiler.GateSynthesis.placeHom e₁ U).val := by
  apply basisInsertion_intertwines
  intro x
  obtain ⟨⟨i,t⟩,rfl⟩ := e₁.surjective x
  rw [hf,placeHom_basis_sum,placeHom_basis_sum,Matrix.mulVec_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mulVec_smul,basisInsertion_basis,hf]

/-- Scratch extension preserves every clean column for every oracle. -/
theorem scratchPort_intertwines (e : L × T ≃ P) (t₀ : T) (U : Matrix.unitaryGroup L ℂ) :
    ((scratchPort e).apply U).val*basisInsertion (fun x => e (x,t₀))=
      basisInsertion (fun x => e (x,t₀))*U.val := by
  rw [scratchPort_apply]
  ext i j
  obtain ⟨⟨x,s⟩,rfl⟩ := e.surjective i
  simp only [Matrix.mul_apply,basisInsertion]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [placeHom_entry]
  simp [e.injective.eq_iff,Prod.mk.injEq,ite_and,eq_comm]

/-- Tensoring with untouched data preserves a clean-subspace simulation. -/
theorem tensor_intertwines {D : Type*} [Fintype D] [DecidableEq D]
    (f : L → P) (U : Matrix.unitaryGroup P ℂ) (V : Matrix.unitaryGroup L ℂ)
    (h : U.val*basisInsertion f=basisInsertion f*V.val) :
    (TransducerCompiler.GateSynthesis.placeHom (Equiv.refl (P × D)) U).val *
        basisInsertion (fun x : L × D => (f x.1,x.2))=
      basisInsertion (fun x : L × D => (f x.1,x.2))*
        (TransducerCompiler.GateSynthesis.placeHom (Equiv.refl (L × D)) V).val := by
  change (Matrix.blockDiagonal (fun _ : D => U.val))*_=_*(Matrix.blockDiagonal (fun _ : D => V.val))
  ext ⟨p,e⟩ ⟨x,d⟩
  have hh := congrFun (congrFun h p) x
  simp only [Matrix.mul_apply,basisInsertion] at hh
  by_cases hed : e=d
  · subst e
    simpa [Matrix.mul_apply,basisInsertion,Fintype.sum_prod_type,Matrix.blockDiagonal,ite_and] using hh
  · simp [Matrix.mul_apply,basisInsertion,Fintype.sum_prod_type,Matrix.blockDiagonal,ite_and,hed]

/-- Associating a spectator tensor does not alter physical placement. -/
theorem placeHom_tensor_assoc {K R D : Type*} [Fintype K] [DecidableEq K]
    [Fintype R] [DecidableEq R] [Fintype D] [DecidableEq D]
    (U : Matrix.unitaryGroup K ℂ) :
    TransducerCompiler.GateSynthesis.placeHom (Equiv.refl ((K × R) × D))
      (TransducerCompiler.GateSynthesis.placeHom (Equiv.refl (K × R)) U)=
    TransducerCompiler.GateSynthesis.placeHom (Equiv.prodAssoc K R D).symm U := by
  apply Subtype.ext
  change (Matrix.blockDiagonal (fun _ : D => Matrix.blockDiagonal (fun _ : R => U.val))) = _
  ext ⟨⟨x,r⟩,d⟩ ⟨⟨y,s⟩,e⟩
  change (if d=e then (if r=s then U.val x y else 0) else 0)=
    (if (r,d)=(s,e) then U.val x y else 0)
  by_cases hr : r=s <;> by_cases hd : d=e <;> simp [hr,hd]

/-- Matrix intertwining composes in execution order. -/
theorem intertwines_mul (J : Matrix P L ℂ) (U V : Matrix P P ℂ) (u v : Matrix L L ℂ)
    (hU : U*J=J*u) (hV : V*J=J*v) : (V*U)*J=J*(v*u) := by
  rw [Matrix.mul_assoc,hU,← Matrix.mul_assoc V,hV,Matrix.mul_assoc]

end OptimalQLS.PolynomialTransform
