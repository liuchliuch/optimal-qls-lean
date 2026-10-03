import OptimalQLS.TransducerCompiler.Physical.Safety
import OptimalQLS.PhysicalPadding.Basis

/-! Exact clean-register norm transport for the literal emitted compiler. -/
noncomputable section
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
open scoped Classical
namespace OptimalQLS.TransducerCompiler.Physical
open Matrix BinaryClock PolynomialTransform

def cleanVector (m ℓ : ℕ) (v : SynthSpace (Bits m) ℓ → ℂ) : Space m ℓ → ℂ :=
  basisInsertion (clean m ℓ)*ᵥv

theorem cleanVector_norm (m ℓ : ℕ) (v : SynthSpace (Bits m) ℓ → ℂ) :
    ‖WithLp.toLp 2 (cleanVector m ℓ v)‖=‖WithLp.toLp 2 v‖ := by
  let f : SynthSpace (Bits m) ℓ ↪ Space m ℓ := ⟨clean m ℓ,fun _ _ he=>congrArg Prod.fst he⟩
  change ‖PhysicalPadding.coordinateIsometry f (WithLp.toLp 2 v)‖=‖WithLp.toLp 2 v‖
  exact (PhysicalPadding.coordinateIsometry f).norm_map _

theorem compile_apply (m ℓ : ℕ) (hℓ : 0<ℓ)
    (S : Matrix.unitaryGroup (Base (Bits m)) ℂ) (work : WorkCircuit m)
    (hw : ControlledWork S work) (c : SynthCircuit ℓ) (U₁ U₂ : Matrix.unitaryGroup (Bits m) ℂ)
    (v : SynthSpace (Bits m) ℓ → ℂ) :
    (((compile m ℓ work c).toQuery (gateEval m ℓ hℓ)).eval U₁ U₂).val*ᵥcleanVector m ℓ v=
      cleanVector m ℓ ((c.eval S U₁ U₂).val*ᵥv) := by
  have he:=congrArg (fun M=>M*ᵥv) (compile_intertwines m ℓ hℓ S work hw c U₁ U₂)
  simpa only [Matrix.mulVec_mulVec,cleanVector] using he

theorem compile_error_eq (m ℓ : ℕ) (hℓ : 0<ℓ)
    (S : Matrix.unitaryGroup (Base (Bits m)) ℂ) (work : WorkCircuit m)
    (hw : ControlledWork S work) (c : SynthCircuit ℓ) (U₁ U₂ : Matrix.unitaryGroup (Bits m) ℂ)
    (v w : SynthSpace (Bits m) ℓ → ℂ) :
    ‖WithLp.toLp 2 ((((compile m ℓ work c).toQuery (gateEval m ℓ hℓ)).eval U₁ U₂).val*ᵥ
      cleanVector m ℓ v-cleanVector m ℓ w)‖=
      ‖WithLp.toLp 2 ((c.eval S U₁ U₂).val*ᵥv-w)‖ := by
  rw [compile_apply m ℓ hℓ S work hw c U₁ U₂]
  have he : cleanVector m ℓ ((c.eval S U₁ U₂).val*ᵥv)-cleanVector m ℓ w=
      cleanVector m ℓ ((c.eval S U₁ U₂).val*ᵥv-w) := by
    unfold cleanVector
    rw [Matrix.mulVec_sub]
  rw [he,cleanVector_norm]

end OptimalQLS.TransducerCompiler.Physical
