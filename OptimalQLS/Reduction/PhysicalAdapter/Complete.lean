import OptimalQLS.Reduction.PhysicalAdapter.Provenance

/-! One fixed actual normalized solver, implemented using arbitrary original oracles. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
open scoped Classical
namespace OptimalQLS.Reduction.PhysicalAdapter
open Matrix PolynomialTransform TransducerCompiler BinaryClock Refinement.PhysicalProgram
variable {a n : ℕ} {κ s ŝ ε : ℝ} {h : BudgetParameters κ s ŝ}

def adapted (I : Implementation a (n+1) (ε := ε) h) : Circuit a n (preparationExponent κ) :=
  substitute a n _ I.circuit

theorem implementation_allowed (I : Implementation a (n+1) (ε := ε) h) : Allowed I.circuit := by
  constructor
  · exact program_matrix_ports a (n+1) _ I.preparation I.preparation_strict
      I.filter I.filter_ports I.correction I.correction_ports
  · exact program_vector_ports a (n+1) _ I.preparation I.preparation_strict
      I.filter I.filter_vector I.correction I.correction_vector

theorem adapted_intertwines (I : Implementation a (n+1) (ε := ε) h)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    (((adapted I).toQuery (gateEval a n _ (Preparation.CompilerAttachment.preparationExponent_pos h))).eval UA Ub).val *
      basisInsertion (clean a n _)=basisInsertion (clean a n _)*
        ((I.circuit.toQuery (Refinement.PhysicalProgram.gateEval a (n+1) _
          (Preparation.CompilerAttachment.preparationExponent_pos h))).eval (matrixOracle UA) (vectorOracle Ub)).val :=
  substitute_intertwines a n _ _ I.circuit (implementation_allowed I) UA Ub

/-- The matrix identity preserves every coherent old input, with clean scratch returned. -/
theorem adapted_apply (I : Implementation a (n+1) (ε := ε) h)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (v : Register a (n+1) (preparationExponent κ) → ℂ) :
    (((adapted I).toQuery (gateEval a n _ (Preparation.CompilerAttachment.preparationExponent_pos h))).eval UA Ub).val *ᵥ
      (basisInsertion (clean a n _)*ᵥv)=basisInsertion (clean a n _)*ᵥ
        (((I.circuit.toQuery (Refinement.PhysicalProgram.gateEval a (n+1) _
          (Preparation.CompilerAttachment.preparationExponent_pos h))).eval (matrixOracle UA) (vectorOracle Ub)).val*ᵥv) := by
  simpa only [Matrix.mulVec_mulVec] using congrArg (fun M=>M*ᵥv) (adapted_intertwines I UA Ub)

theorem adapted_counts (I : Implementation a (n+1) (ε := ε) h) :
    ((adapted I).toQuery (gateEval a n _ (Preparation.CompilerAttachment.preparationExponent_pos h))).matrixQueries=
      2*(I.circuit.toQuery (Refinement.PhysicalProgram.gateEval a (n+1) _
        (Preparation.CompilerAttachment.preparationExponent_pos h))).matrixQueries ∧
    ((adapted I).toQuery (gateEval a n _ (Preparation.CompilerAttachment.preparationExponent_pos h))).vectorQueries=
      (I.circuit.toQuery (Refinement.PhysicalProgram.gateEval a (n+1) _
        (Preparation.CompilerAttachment.preparationExponent_pos h))).vectorQueries ∧
    (adapted I).workGates≤I.circuit.workGates+
      4801*(I.circuit.toQuery (Refinement.PhysicalProgram.gateEval a (n+1) _
        (Preparation.CompilerAttachment.preparationExponent_pos h))).matrixQueries :=
  substitute_counts a n _ _ I.circuit

/-- Exactly three fresh shared scratch bits; the fourth extra bit is the live data head. -/
theorem space_card (a n ℓ : ℕ) : Fintype.card (Space a n ℓ)=2^(n+3*a+2*ℓ+31) := by
  rw [Fintype.card_prod,register_card]
  have hs : Fintype.card PhaseScratch=2^3 := by decide
  rw [hs,←pow_add]
  congr 1
  omega

@[simp] theorem adapted_forScale (I : Implementation a (n+1) (ε := ε) h)
    {t : ℝ} (h' : BudgetParameters κ t ŝ) : adapted (I.forScale h')=adapted I := rfl

theorem adapted_safe (I : Implementation a (n+1) (ε := ε) h) : Safe (adapted I) :=
  substitute_safe a n _ (Preparation.CompilerAttachment.preparationExponent_pos h) I.circuit


end OptimalQLS.Reduction.PhysicalAdapter
