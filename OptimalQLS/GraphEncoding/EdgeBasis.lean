import OptimalQLS.GraphEncoding.ControlledGates

/-! # Exact target-wire semantics of every reversible edge primitive -/
noncomputable section
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 1000000
namespace OptimalQLS.GraphEncoding
open Matrix TransducerCompiler PolynomialTransform
open BinaryClock
variable {a b w : Type*} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype w] [DecidableEq w]

/-- Placement preserves arbitrary finite basis expansions, not only permutations. -/
theorem placeHom_basis_expansion {Y : Type*} [Fintype Y]
    (e : a × b ≃ w) (U : Matrix.unitaryGroup a ℂ) (i : a) (s : b)
    (out : Y → a) (coef : Y → ℂ)
    (h : U.val *ᵥ Pi.single i 1 = ∑ y, coef y • (Pi.single (out y) 1 : a → ℂ)) :
    (TransducerCompiler.GateSynthesis.placeHom e U).val *ᵥ Pi.single (e (i,s)) 1 =
      ∑ y, coef y • (Pi.single (e (out y,s)) 1 : w → ℂ) := by
  have he := scratchPort_intertwines e s U
  rw [scratchPort_apply] at he
  rw [← basisInsertion_basis (fun x => e (x,s)), Matrix.mulVec_mulVec, he,
    ← Matrix.mulVec_mulVec, h, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, basisInsertion_basis]

theorem template_input (c d t : Fin 4) (hcd : c≠d) (hct : c≠t) (hdt : d≠t)
    (z : Bool) (x : LabelBits) :
    TransducerCompiler.GateSynthesis.templateWiring c d t hcd hct hdt
      ((z,(x c,x d,x t)), fun i => x i.val) = (z,x) := by
  change (z,(TransducerCompiler.GateSynthesis.splitTriple c d t hcd hct hdt).symm
    ((TransducerCompiler.GateSynthesis.splitTriple c d t hcd hct hdt) x)) = _
  rw [Equiv.symm_apply_apply]

theorem compute_rotate_basis (θ : ℝ) (z a b y : Bool) :
    (RealToffoli.ComputeGate.eval (.rotate θ)).val *ᵥ Pi.single (z,(a,b,y)) 1 =
      ∑ r : Bool, (complexifyRealUnitary (RealToffoli.rotationReal θ)).val r z •
        (Pi.single (r,(a,b,y)) 1 : RealToffoli.State → ℂ) := by
  have he : RealToffoli.ComputeGate.eval (.rotate θ) =
      TransducerCompiler.GateSynthesis.placeHom (Equiv.refl (Bool × RealToffoli.Sector))
        (complexifyRealUnitary (RealToffoli.rotationReal θ)) := by
    apply Subtype.ext
    ext i j
    simp [placeHom_entries, RealToffoli.ComputeGate.eval, RealToffoli.ComputeGate.small,
      RealToffoli.block, Matrix.blockDiagonal_apply, RealToffoli.complexifyHom]
  rw [he]
  exact placeHom_basis_sum _ _ z (a,b,y)

theorem compute_controlA_basis (z a b y : Bool) :
    (RealToffoli.ComputeGate.eval .controlA).val *ᵥ Pi.single (z,(a,b,y)) 1 =
      Pi.single (Bool.xor z a,(a,b,y)) 1 := by
  ext ⟨r,s⟩
  simp only [Matrix.mulVec_single_one, Matrix.col_apply]
  by_cases hs : s=(a,b,y)
  · subst s
    cases a <;> cases z <;> cases r <;>
      simp [RealToffoli.ComputeGate.eval, RealToffoli.ComputeGate.small,
        RealToffoli.block, Matrix.blockDiagonal_apply, RealToffoli.complexifyHom,
        complexifyRealUnitary, RealToffoli.controlledX, RealToffoli.xReal,
        RealToffoli.xEntry, Pi.single_apply, Matrix.one_apply]
  · simp [RealToffoli.ComputeGate.eval, RealToffoli.block, Matrix.blockDiagonal_apply,
      hs, Pi.single_apply, Prod.mk.injEq]

theorem compute_controlB_basis (z a b y : Bool) :
    (RealToffoli.ComputeGate.eval .controlB).val *ᵥ Pi.single (z,(a,b,y)) 1 =
      Pi.single (Bool.xor z b,(a,b,y)) 1 := by
  ext ⟨r,s⟩
  simp only [Matrix.mulVec_single_one, Matrix.col_apply]
  by_cases hs : s=(a,b,y)
  · subst s
    cases b <;> cases z <;> cases r <;>
      simp [RealToffoli.ComputeGate.eval, RealToffoli.ComputeGate.small,
        RealToffoli.block, Matrix.blockDiagonal_apply, RealToffoli.complexifyHom,
        complexifyRealUnitary, RealToffoli.controlledX, RealToffoli.xReal,
        RealToffoli.xEntry, Pi.single_apply, Matrix.one_apply]
  · simp [RealToffoli.ComputeGate.eval, RealToffoli.block, Matrix.blockDiagonal_apply,
      hs, Pi.single_apply, Prod.mk.injEq]

theorem edge_rotate_basis (c d t : Fin 4) (hcd : c≠d) (hct : c≠t) (hdt : d≠t)
    (θ : ℝ) (z : Bool) (x : LabelBits) :
    (TransducerCompiler.GateSynthesis.LowerGate.eval
      (.template c d t hcd hct hdt (.atom (.rotate θ)))).val *ᵥ Pi.single (z,x) 1 =
      ∑ r : Bool, (complexifyRealUnitary (RealToffoli.rotationReal θ)).val r z •
        (Pi.single (r,x) 1 : TransducerCompiler.GateSynthesis.Space (Fin 4) → ℂ) := by
  have hh := placeHom_basis_expansion
    (TransducerCompiler.GateSynthesis.templateWiring c d t hcd hct hdt)
    (RealToffoli.ComputeGate.eval (.rotate θ)) (z,(x c,x d,x t))
    (fun i => x i.val) (fun r => (r,(x c,x d,x t)))
    (fun r => (complexifyRealUnitary (RealToffoli.rotationReal θ)).val r z)
    (compute_rotate_basis θ z (x c) (x d) (x t))
  simpa only [template_input] using hh

theorem edge_controlA_basis (c d t : Fin 4) (hcd : c≠d) (hct : c≠t) (hdt : d≠t)
    (z : Bool) (x : LabelBits) :
    (TransducerCompiler.GateSynthesis.LowerGate.eval
      (.template c d t hcd hct hdt (.atom .controlA))).val *ᵥ Pi.single (z,x) 1 =
      Pi.single (Bool.xor z (x c),x) 1 := by
  have hh := TransducerCompiler.GateSynthesis.placeHom_basis
    (TransducerCompiler.GateSynthesis.templateWiring c d t hcd hct hdt)
    (RealToffoli.ComputeGate.eval .controlA) (z,(x c,x d,x t))
    (Bool.xor z (x c),(x c,x d,x t)) (fun i => x i.val)
    (compute_controlA_basis z (x c) (x d) (x t))
  simpa only [template_input] using hh

theorem edge_controlB_basis (c d t : Fin 4) (hcd : c≠d) (hct : c≠t) (hdt : d≠t)
    (z : Bool) (x : LabelBits) :
    (TransducerCompiler.GateSynthesis.LowerGate.eval
      (.template c d t hcd hct hdt (.atom .controlB))).val *ᵥ Pi.single (z,x) 1 =
      Pi.single (Bool.xor z (x d),x) 1 := by
  have hh := TransducerCompiler.GateSynthesis.placeHom_basis
    (TransducerCompiler.GateSynthesis.templateWiring c d t hcd hct hdt)
    (RealToffoli.ComputeGate.eval .controlB) (z,(x c,x d,x t))
    (Bool.xor z (x d),(x c,x d,x t)) (fun i => x i.val)
    (compute_controlB_basis z (x c) (x d) (x t))
  simpa only [template_input] using hh

theorem template_target_update (c d t : Fin 4) (hcd : c≠d) (hct : c≠t) (hdt : d≠t)
    (z y : Bool) (x : LabelBits) :
    TransducerCompiler.GateSynthesis.templateWiring c d t hcd hct hdt
      ((z,(x c,x d,y)), fun i => x i.val) = (z,Function.update x t y) := by
  apply Prod.ext
  · rfl
  · funext i
    by_cases hic : i=c <;> by_cases hid : i=d <;> by_cases hit : i=t <;>
      simp_all [TransducerCompiler.GateSynthesis.templateWiring,
        TransducerCompiler.GateSynthesis.splitTriple, Function.update_apply] <;> aesop

theorem edge_copy_basis (c d t : Fin 4) (hcd : c≠d) (hct : c≠t) (hdt : d≠t)
    (z : Bool) (x : LabelBits) :
    (TransducerCompiler.GateSynthesis.LowerGate.eval
      (.template c d t hcd hct hdt .copy)).val *ᵥ Pi.single (z,x) 1 =
      Pi.single (z,Function.update x t (Bool.xor (x t) z)) 1 := by
  have hh := TransducerCompiler.GateSynthesis.placeHom_basis
    (TransducerCompiler.GateSynthesis.templateWiring c d t hcd hct hdt)
    RealToffoli.copyUnitary (z,(x c,x d,x t))
    (z,(x c,x d,Bool.xor (x t) z)) (fun i => x i.val)
    (RealToffoli.copy_basis z (x c) (x d) (x t))
  simpa only [template_input, template_target_update] using hh


theorem edge_x_basis (t : Fin 4) (z : Bool) (x : LabelBits) :
    (TransducerCompiler.GateSynthesis.LowerGate.eval (.x t)).val *ᵥ Pi.single (z,x) 1 =
      Pi.single (z,Function.update x t (!(x t))) 1 := by
  have hh := GraphEncoding.GateSynthesis.dataHom_basis (programUnitary [BinaryClock.Gate.x t]) z x _
    (programUnitary_basis [BinaryClock.Gate.x t] x)
  simpa only [TransducerCompiler.GateSynthesis.LowerGate.eval,run_cons,run_nil,BinaryClock.Gate.act] using hh

theorem edge_cx_basis (c t : Fin 4) (hct : c≠t) (z : Bool) (x : LabelBits) :
    (TransducerCompiler.GateSynthesis.LowerGate.eval (.cx c t hct)).val *ᵥ Pi.single (z,x) 1 =
      Pi.single (z,Function.update x t (Bool.xor (x t) (x c))) 1 := by
  have hh := GraphEncoding.GateSynthesis.dataHom_basis (programUnitary [BinaryClock.Gate.cx c t hct]) z x _
    (programUnitary_basis [BinaryClock.Gate.cx c t hct] x)
  simpa only [TransducerCompiler.GateSynthesis.LowerGate.eval,run_cons,run_nil,BinaryClock.Gate.act] using hh

end OptimalQLS.GraphEncoding
