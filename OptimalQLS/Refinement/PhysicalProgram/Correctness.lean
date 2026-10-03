import OptimalQLS.Refinement.PhysicalProgram.State
import OptimalQLS.PhysicalPadding.Registers
import OptimalQLS.PhysicalPadding.Refinement

/-! # Physical run correctness on any computationally embedded active subspace -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open scoped Classical Matrix.Norms.L2Operator
namespace OptimalQLS.Refinement.PhysicalProgram
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform PhysicalPadding

/-- The exact joint accepting branch of the emitted whole run. -/
def acceptedVector (a n ℓ : ℕ) (hℓ : 0<ℓ)
    (cp : CompilerAttachment.Circuit a n ℓ)
    (cf : GraphAttachedCircuit a (Bits n) (Bits n)) (cc : SingleFlagCircuit a (Bits n) (Bits n))
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    EuclideanSpace ℂ (Bits n) :=
  WithLp.toLp 2 (accepted (prepZero a ℓ) (physicalZero (a+4)) (physicalZero a)
    ((((program a n ℓ cp cf cc).toQuery (gateEval a n ℓ hℓ)).eval UA Ub).val*ᵥ
      Pi.single (initial a n ℓ) 1))

/-- No global inverse, data-support promise, or naturality condition is imposed
on the supplied physical oracle. Active support is derived from preparation. -/
theorem program_correctness {D : Type*} [Fintype D] [DecidableEq D]
    (a n : ℕ) (f : D ↪ Bits n) {κ s ŝ ε : ℝ} (h : BudgetParameters κ s ŝ)
    (cp : CompilerAttachment.Circuit a n (preparationExponent κ))
    (cf : GraphAttachedCircuit a (Bits n) (Bits n)) (cc : SingleFlagCircuit a (Bits n) (Bits n))
    (hprep : ∀ UA Ub, ((cp.toQuery (CompilerAttachment.gateEval a n _ (CompilerAttachment.preparationExponent_pos h))).eval UA Ub).val *ᵥ
      Pi.single (CompilerAttachment.allZero a n (preparationExponent κ)) 1=
      basisInsertion (CompilerAttachment.clean a n (preparationExponent κ))*ᵥ
        originalPreparedState (fun _ : Fin a=>false) (fun _ : Fin n=>false) h UA Ub)
    (A : Matrix D D ℂ) (hA : A.IsHermitian) (hunit : IsUnit A)
    (hinv : ‖Ring.inverse A‖≤κ) (hε0 : 0<ε) (hε1 : ε<1/2)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (henc : IsBlockEncoding (fun _ : Fin a=>false) 1 0 UA (zeroExtend f A))
    (Ub : Matrix.unitaryGroup (Bits n) ℂ) (b : EuclideanSpace ℂ D) (hb : ‖b‖=1)
    (hcol : ∀ i, Ub i (fun _ : Fin n=>false)=coordinateIsometry f b i)
    (hs : s=solutionScale 1 A b)
    (hf : IsBlockEncoding (physicalZero (a+4)) 1 0 ((cf.toQuery (GraphAttachedGate.eval a)).eval UA Ub)
      (Polynomial.aeval (GraphEncoding.normalizedGraph (zeroExtend f A) κ)
        (liftReal (kernelFilter (graphFilterGap κ) (ε/1024)))))
    (hc : IsBlockEncoding (physicalZero a) 1 0 ((cc.toQuery (SingleFlagGate.eval a)).eval UA Ub)
      (Polynomial.aeval (zeroExtend f A) (liftReal (paperCorrectionPolynomial κ (ε/1024))))) :
    let z := acceptedVector a n _ (CompilerAttachment.preparationExponent_pos h) cp cf cc UA Ub
    let x := coordinateIsometry f
      (NormedSpace.normalize (Ring.inverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) b))
    z≠0 ∧ ‖NormedSpace.normalize z-x‖≤ε/2 ∧ 1/65536<‖z‖^2 := by
  haveI : Nonempty D := by
    by_contra hn
    haveI : IsEmpty D := not_nonempty_iff.mp hn
    have hz : b=0 := Subsingleton.elim _ _
    have he : (0:ℝ)=1 := by simpa [hz] using hb
    norm_num at he
  dsimp only [acceptedVector]
  rw [program_polynomial_acceptance a n h cp cf cc hprep UA Ub _ hf hc]
  have hp := physical_original_preparation_coarse f (fun _ : Fin a=>false)
    (fun _ : Fin n=>false) h A hA hunit hinv UA henc Ub b hb hcol hs
  dsimp only at hp
  obtain ⟨hsupport,hn,β,hβ0,hβ1,hPy,_⟩ := hp
  have hy := (zeroAuxiliaryOutput_norm_le (GraphEncoding.physicalSignalZero (fun _ : Fin a=>false))
    (originalPreparedState (fun _ : Fin a=>false) (fun _ : Fin n=>false) h UA Ub)).trans_eq hn
  have hAnorm : ‖A‖≤1 := by
    rw [←zeroExtend_norm f A]
    exact norm_le_of_exact_block henc
  exact physical_refinement_component_guarantee f A hA hunit hAnorm h.kappa_ge_two hinv hε0 hε1
    b hb _ hy hsupport hβ0.le hβ1 hPy

end OptimalQLS.Refinement.PhysicalProgram
