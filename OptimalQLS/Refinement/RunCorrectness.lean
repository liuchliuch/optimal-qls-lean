import OptimalQLS.Refinement.Run
import OptimalQLS.Preparation.BasisInput
import OptimalQLS.PhysicalPadding.Refinement

/-! # Exact accepted vector of one complete supplied-oracle run -/
noncomputable section
namespace OptimalQLS.Refinement
open Matrix Preparation Alignment TransducerCompiler BinaryClock PolynomialTransform
open scoped Matrix.Norms.L2Operator
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
variable {S D F C A B : Type*} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]
  [Fintype F] [DecidableEq F] [Fintype C] [DecidableEq C]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def runBasisIndex (s₀ : S) (i₀ : D) (f₀ : F) (c₀ : C) (ℓ : ℕ) :
    Space (CoarseAux S ℓ) F C D := (c₀,(coarseZero s₀ ℓ,(f₀,(1,i₀))))

theorem preparationBasisInput_joint (s₀ : S) (i₀ : D) (f₀ : F) (c₀ : C)
    {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ) :
    jointInput f₀ c₀ (preparationBasisInput s₀ i₀ h ∘
      coarseWiring (GraphEncoding.PhysicalSignal S) D (preparationExponent κ))=
    Pi.single (runBasisIndex (GraphEncoding.physicalSignalZero s₀) i₀ f₀ c₀ (preparationExponent κ)) 1 := by
  rw [preparationBasisInput_single]
  ext ⟨c,⟨syn,spare,sig,l,t,cache⟩,f,g,i⟩
  simp [jointInput,coarseWiring,preparationBasisIndex,runBasisIndex,coarseZero,Pi.single_apply,
    Function.comp_apply,ite_and]
  split_ifs <;> rfl

/-- The complete coherent circuit starts from a literal computational basis. -/
theorem fullRunProgram_prepared_state (s₀ : S) (i₀ : D) (f₀ : F) (c₀ : C)
    {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ)
    (cf : QueryCircuit (S × D) D (F × (Fin 4 × D)))
    (cc : QueryCircuit (S × D) D (C × D))
    (UA : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup D ℂ) :
    ((fullRunProgram (originalPreparationAlgorithm s₀ i₀ h) cf cc).eval UA Ub).val*ᵥ
      Pi.single (runBasisIndex (GraphEncoding.physicalSignalZero s₀) i₀ f₀ c₀ (preparationExponent κ)) 1=
    ((refinementProgram cf cc).eval UA Ub).val*ᵥjointInput f₀ c₀
      (originalPreparedState s₀ i₀ h UA Ub ∘
        coarseWiring (GraphEncoding.PhysicalSignal S) D (preparationExponent κ)) := by
  rw [← preparationBasisInput_joint s₀ i₀ f₀ c₀ h]
  exact fullRunProgram_state _ _ _ UA Ub f₀ c₀ _

/-- The block-polynomial equalities identify the actual joint branch with the
literal filter/correction composition, including a singular padded operator. -/
theorem refinementProgram_polynomial_branch {P : Type*} [Fintype P] [DecidableEq P]
    (cf : QueryCircuit A B (F × (Fin 4 × D))) (cc : QueryCircuit A B (C × D))
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (M : Matrix D D ℂ) (κ ε : ℝ) (p₀ : P) (f₀ : F) (c₀ : C)
    (hf : IsBlockEncoding f₀ 1 0 (cf.eval UA Ub)
      (Polynomial.aeval (GraphEncoding.normalizedGraph M κ)
        (liftReal (kernelFilter (graphFilterGap κ) (ε/1024)))))
    (hc : IsBlockEncoding c₀ 1 0 (cc.eval UA Ub)
      (Polynomial.aeval M (liftReal (paperCorrectionPolynomial κ (ε/1024)))))
    (Ψ : P × (Fin 4 × D) → ℂ) :
    WithLp.toLp 2 (accepted p₀ f₀ c₀ (((refinementProgram cf cc).eval UA Ub).val*ᵥ
      jointInput f₀ c₀ Ψ))=
    PhysicalPadding.refinementAccepted M κ ε (WithLp.toLp 2 (fun x=>Ψ (p₀,x))) := by
  have hfb := exact_block_eq hf
  have hcb := exact_block_eq hc
  rw [one_smul] at hfb hcb
  rw [refinementProgram_acceptance,←hfb,←hcb]
  unfold PhysicalPadding.refinementAccepted PhysicalPadding.refinementFilter
  rw [←polynomial_matrix_to_operator]
  rfl

/-- Actual original-oracle preparation, exact polynomial circuits, and one
coordinate acceptance yield the physical solution, without an assumed output
support or coarse-state certificate. -/
theorem fullRunProgram_physical_correctness {d : ℕ} [NeZero d]
    (s₀ : S) (f₀ : F) (c₀ : C) {κ s ŝ ε : ℝ} (h : BudgetParameters κ s ŝ)
    (cf : QueryCircuit (S × PhysicalPadding.PhysicalData d) (PhysicalPadding.PhysicalData d)
      (F × (Fin 4 × PhysicalPadding.PhysicalData d)))
    (cc : QueryCircuit (S × PhysicalPadding.PhysicalData d) (PhysicalPadding.PhysicalData d)
      (C × PhysicalPadding.PhysicalData d))
    (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.IsHermitian) (hunit : IsUnit M)
    (hinv : ‖Ring.inverse M‖≤κ) (hε0 : 0<ε) (hε1 : ε<1/2)
    (UA : Matrix.unitaryGroup (S × PhysicalPadding.PhysicalData d) ℂ)
    (henc : IsBlockEncoding s₀ 1 0 UA (PhysicalPadding.physicalMatrix M))
    (Ub : Matrix.unitaryGroup (PhysicalPadding.PhysicalData d) ℂ)
    (b : DataSpace d) (hb : ‖b‖=1)
    (hcol : ∀ i,Ub i 0=PhysicalPadding.activeIsometry d b i)
    (hs : s=solutionScale 1 M b)
    (hf : IsBlockEncoding f₀ 1 0 (cf.eval UA Ub)
      (Polynomial.aeval (GraphEncoding.normalizedGraph (PhysicalPadding.physicalMatrix M) κ)
        (liftReal (kernelFilter (graphFilterGap κ) (ε/1024)))))
    (hc : IsBlockEncoding c₀ 1 0 (cc.eval UA Ub)
      (Polynomial.aeval (PhysicalPadding.physicalMatrix M)
        (liftReal (paperCorrectionPolynomial κ (ε/1024))))) :
    let c := fullRunProgram (originalPreparationAlgorithm s₀ (0 : PhysicalPadding.PhysicalData d) h) cf cc
    let z := WithLp.toLp 2 (accepted (coarseZero (GraphEncoding.physicalSignalZero s₀) (preparationExponent κ))
      f₀ c₀ ((c.eval UA Ub).val*ᵥPi.single
        (runBasisIndex (GraphEncoding.physicalSignalZero s₀) (0 : PhysicalPadding.PhysicalData d)
          f₀ c₀ (preparationExponent κ)) 1))
    z≠0 ∧ ‖NormedSpace.normalize z-PhysicalPadding.physicalSolution M b‖≤ε/2 ∧
      1/65536<‖z‖^2 := by
  dsimp only
  rw [fullRunProgram_prepared_state,refinementProgram_polynomial_branch cf cc UA Ub _ κ ε _ f₀ c₀ hf hc]
  exact PhysicalPadding.physical_preparation_refinement_guarantee s₀ h M hM hunit hinv hε0 hε1
    UA henc Ub b hb hcol hs

end OptimalQLS.Refinement
