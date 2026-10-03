import OptimalQLS.Refinement.PhysicalProgram.Circuit

/-! # Exact coherent state and joint accepted vector of the physical run -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.Refinement.PhysicalProgram
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform

theorem preparationPort_basis (a n ℓ : ℕ)
    (U : Matrix.unitaryGroup (CompilerAttachment.Physical a n ℓ) ℂ)
    (x : CompilerAttachment.Physical a n ℓ) (f₀ : FilterSignal a) (c₀ : CorrectionSignal a) :
    ((preparationPort a n ℓ).apply U).val*ᵥ
      Pi.single (preparationFrame a n ℓ (x,(c₀,f₀))) 1=
      jointInput f₀ c₀ ((U.val*ᵥPi.single x 1) ∘ (preparationCoordinates a n ℓ).symm) := by
  have hb : jointInput f₀ c₀ (Pi.single (preparationCoordinates a n ℓ x) 1)=
      Pi.single (preparationFrame a n ℓ (x,(c₀,f₀))) (1:ℂ) := by
    ext ⟨c,p,f,d⟩
    simp [jointInput,preparationFrame,preparationRunWiring,Pi.single_apply,Prod.mk.injEq,ite_and]
    split_ifs <;> simp_all [Prod.ext_iff]
  rw [preparationPort_relabel,←hb,preparationRunPort_input,rewire_apply]
  have hx : (Pi.single (preparationCoordinates a n ℓ x) (1:ℂ)) ∘ preparationCoordinates a n ℓ=
      Pi.single x 1 := by
    funext y
    simp [Pi.single_apply,(preparationCoordinates a n ℓ).injective.eq_iff]
  rw [hx]

theorem program_state (a n ℓ : ℕ) (hℓ : 0<ℓ)
    (cp : CompilerAttachment.Circuit a n ℓ)
    (cf : GraphAttachedCircuit a (Bits n) (Bits n))
    (cc : SingleFlagCircuit a (Bits n) (Bits n))
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    (((program a n ℓ cp cf cc).toQuery (gateEval a n ℓ hℓ)).eval UA Ub).val *ᵥ
      Pi.single (initial a n ℓ) 1=
      ((refinementProgram (P := PrepAux a ℓ) (cf.toQuery (GraphAttachedGate.eval a))
        (cc.toQuery (SingleFlagGate.eval a))).eval UA Ub).val *ᵥ
      jointInput (physicalZero (a+4)) (physicalZero a)
        ((((cp.toQuery (CompilerAttachment.gateEval a n ℓ hℓ)).eval UA Ub).val *ᵥ
          Pi.single (CompilerAttachment.allZero a n ℓ) 1) ∘ (preparationCoordinates a n ℓ).symm) := by
  rw [program_toQuery,QueryCircuit.eval_append,Submonoid.coe_mul,←Matrix.mulVec_mulVec,
    QueryCircuit.lift_eval]
  exact congrArg (fun v => ((refinementProgram (P := PrepAux a ℓ)
    (cf.toQuery (GraphAttachedGate.eval a)) (cc.toQuery (SingleFlagGate.eval a))).eval UA Ub).val*ᵥv)
    (preparationPort_basis a n ℓ _ _ _ _)

theorem program_prepared_state (a n : ℕ) {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ)
    (cp : CompilerAttachment.Circuit a n (preparationExponent κ))
    (cf : GraphAttachedCircuit a (Bits n) (Bits n))
    (cc : SingleFlagCircuit a (Bits n) (Bits n))
    (hprep : ∀ UA Ub, ((cp.toQuery (CompilerAttachment.gateEval a n _ (CompilerAttachment.preparationExponent_pos h))).eval UA Ub).val *ᵥ
      Pi.single (CompilerAttachment.allZero a n (preparationExponent κ)) 1=
      basisInsertion (CompilerAttachment.clean a n (preparationExponent κ))*ᵥ
        originalPreparedState (fun _ : Fin a=>false) (fun _ : Fin n=>false) h UA Ub)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    (((program a n _ cp cf cc).toQuery (gateEval a n _ (CompilerAttachment.preparationExponent_pos h))).eval UA Ub).val *ᵥ
      Pi.single (initial a n (preparationExponent κ)) 1=
      ((refinementProgram (P := PrepAux a (preparationExponent κ)) (cf.toQuery (GraphAttachedGate.eval a))
        (cc.toQuery (SingleFlagGate.eval a))).eval UA Ub).val *ᵥ
      jointInput (physicalZero (a+4)) (physicalZero a)
        (coarseVector a n (preparationExponent κ)
          (originalPreparedState (fun _ : Fin a=>false) (fun _ : Fin n=>false) h UA Ub)) := by
  rw [program_state,hprep]
  rfl

theorem program_polynomial_acceptance (a n : ℕ) {κ s ŝ ε : ℝ} (h : BudgetParameters κ s ŝ)
    (cp : CompilerAttachment.Circuit a n (preparationExponent κ))
    (cf : GraphAttachedCircuit a (Bits n) (Bits n))
    (cc : SingleFlagCircuit a (Bits n) (Bits n))
    (hprep : ∀ UA Ub, ((cp.toQuery (CompilerAttachment.gateEval a n _ (CompilerAttachment.preparationExponent_pos h))).eval UA Ub).val *ᵥ
      Pi.single (CompilerAttachment.allZero a n (preparationExponent κ)) 1=
      basisInsertion (CompilerAttachment.clean a n (preparationExponent κ))*ᵥ
        originalPreparedState (fun _ : Fin a=>false) (fun _ : Fin n=>false) h UA Ub)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (M : Matrix (Bits n) (Bits n) ℂ)
    (hf : IsBlockEncoding (physicalZero (a+4)) 1 0 ((cf.toQuery (GraphAttachedGate.eval a)).eval UA Ub)
      (Polynomial.aeval (GraphEncoding.normalizedGraph M κ)
        (liftReal (kernelFilter (graphFilterGap κ) (ε/1024)))))
    (hc : IsBlockEncoding (physicalZero a) 1 0 ((cc.toQuery (SingleFlagGate.eval a)).eval UA Ub)
      (Polynomial.aeval M (liftReal (paperCorrectionPolynomial κ (ε/1024))))) :
    WithLp.toLp 2 (accepted (prepZero a (preparationExponent κ)) (physicalZero (a+4)) (physicalZero a)
      ((((program a n _ cp cf cc).toQuery (gateEval a n _ (CompilerAttachment.preparationExponent_pos h))).eval UA Ub).val *ᵥ
        Pi.single (initial a n (preparationExponent κ)) 1))=
      PhysicalPadding.refinementAccepted M κ ε
        (WithLp.toLp 2 (Alignment.zeroAuxiliaryOutput (GraphEncoding.physicalSignalZero (fun _ : Fin a=>false))
          (originalPreparedState (fun _ : Fin a=>false) (fun _ : Fin n=>false) h UA Ub))) := by
  rw [program_prepared_state a n h cp cf cc hprep]
  rw [refinementProgram_polynomial_branch _ _ UA Ub M κ ε _ _ _ hf hc,coarseVector_slice]

end OptimalQLS.Refinement.PhysicalProgram
