import OptimalQLS.PaperStatements.AppendixA1
import OptimalQLS.Preparation.CompilerAttachment.Complete

/-! # Appendix A.2: the finite preparation circuit

The supplied estimate is independent of the exact solution scale.  The finite
word depends only on the public parameters, and the same word and state occur
in its error, resource, real-gate, cleanup, and original-oracle implementation
clauses.  All geometric and catalyst bounds are derived from the original
normalized Hermitian input; no catalyst or cost certificate is an input.
-/

noncomputable section
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open scoped Classical Matrix.Norms.L2Operator
namespace OptimalQLS.PaperStatements
open Matrix TransducerCompiler TransducerCompiler.BinaryClock
open Preparation Preparation.CompilerAttachment GraphEncoding PolynomialTransform

variable {S D : Type*} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]

/-- The source's ideal `|0⟩|ψ⟩`, in the very same register as the finite output. -/
def appendixA2IdealState (s₀ : S) (i₀ : D) {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ)
    (A : Matrix D D ℂ) (Ub : Matrix.unitaryGroup D ℂ) (b : EuclideanSpace ℂ D) :
    SynthSpace (PreparationData S D) (preparationExponent κ) → ℂ :=
  synthInput h.layout (preparationInternal (physicalSignalZero s₀)
    (preparationOutput (graphMatrix A κ)
      (preparedReflection (signalLift (S := Fin 4) Ub) (1,i₀))
      (overlapMixingParameter κ ŝ) (WithLp.ofLp (graphInput b))))

/-- Discharge every finite-compiler energy hypothesis using the actual graph
matrix of the original input.  In particular, the estimate is not replaced by
the hidden exact solution norm. -/
theorem appendixA2_original_error [Nonempty D] (s₀ : S) (i₀ : D) {κ s ŝ : ℝ}
    (h : BudgetParameters κ s ŝ) (A : Matrix D D ℂ) (hA : A.IsHermitian)
    (hunit : IsUnit A) (hinv : ‖Ring.inverse A‖≤κ)
    (UA : Matrix.unitaryGroup (S × D) ℂ) (henc : IsBlockEncoding s₀ 1 0 UA A)
    (Ub : Matrix.unitaryGroup D ℂ) (b : EuclideanSpace ℂ D) (hb : ‖b‖=1)
    (hcol : ∀ i,Ub i i₀=b i) (hs : s=solutionScale 1 A b) :
    ‖WithLp.toLp 2 (originalPreparedState s₀ i₀ h UA Ub -
      appendixA2IdealState s₀ i₀ h A Ub b)‖ < (1 : ℝ)/1000 := by
  have hα : 0<1+κ⁻¹ := by have := h.kappa_pos; positivity
  have hα2 : 1+κ⁻¹≤2 := by
    have hi : κ⁻¹≤1 := by
      rw [inv_eq_one_div]
      apply (div_le_iff₀ h.kappa_pos).mpr
      linarith [h.kappa_ge_two]
    linarith
  have hblock := exact_block_eq (physicalEncoding_exact κ h.kappa_pos s₀ UA A hA henc)
  have hInv : ‖Ring.inverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A)‖≤κ := by
    rw [← Perturbation.toEuclideanCLM_inverse A hunit]
    exact hinv
  have hp := graphInput_promises A hA
    (hunit.map (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)).toMonoidHom) h.kappa_pos
    (norm_le_of_exact_block henc) hInv b hb
  have hscale : ‖Ring.inverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) b‖=s := by
    rw [← Perturbation.toEuclideanCLM_inverse A hunit]
    simpa only [solutionScale,one_mul] using hs.symm
  dsimp only at hp
  rw [hscale] at hp
  obtain ⟨c,hc,_,_,_,_,_,_,_,he⟩ :=
    finite_preparation_error_uniform (D := Fin 4 × D) (physicalSignalZero s₀) h hα hα2
  subst c
  rw [originalPreparedState_eq s₀ i₀ h UA Ub b hcol]
  exact he (physicalEncoding κ h.kappa_pos UA) (physicalEncoding_hermitian κ h.kappa_pos UA)
    (graphMatrix A κ) (graphMatrix_hermitian A hA κ)
    (signalLift (S := Fin 4) Ub) (1,i₀) (graphInput b) hp.1
    (graphInput_source Ub i₀ b hcol) hblock hp.2.1 hp.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2

/-- A literal controlled-work list supplies the work part of A.2's extra-gate
bound.  Its coherent semantics and cleanup hold for every complete oracle pair,
and every elementary gate is real and acts on at most two qubits. -/
theorem appendixA2_controlled_work (a n : ℕ) {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ) :
    (preparationWorkCode a h).length ≤ 183375*(a+1) ∧
    (∀ g ∈ preparationWorkCode a h,
      g.arity ≤ 2 ∧ Preparation.WorkGates.RealGate g) ∧
    ∀ (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ),
      (((positiveWorkMacro a n (preparationExponent κ) (preparationWorkCode a h)).toQuery
        (positiveWorkGateEval a n (preparationExponent κ) (preparationExponent_pos h))).eval UA Ub).val *
          basisInsertion (clean a n (preparationExponent κ)) =
        basisInsertion (clean a n (preparationExponent κ)) *
          (padHom (cachedWork (finitePreparationWork (D := Fin 4 × Bits n)
            (physicalSignalZero (fun _ : Fin a => false)) h
            (by have := h.kappa_pos; positivity : 0<1+κ⁻¹)))).val := by
  refine ⟨preparationWorkCode_length a h,?_,?_⟩
  · intro g hg
    exact ⟨DirtyAncilla.PhaseGate.arity_le_two g,compiledWorkProgram_real (a+4) _ _ true g hg⟩
  · intro UA Ub
    exact positiveWorkMacro_intertwines a n _ (preparationExponent_pos h) h UA Ub

/-- Source Appendix A.2 with the exact dyadic budgets.  The elementary work
bound uses the implemented controlled-work list above, while the two oracle
counts are the source's `U_H` and `R_e` counts.  One word is selected before the
hidden scale and all complete original oracle unitaries. -/
theorem appendixA2 (a n : ℕ) {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ) :
    ∃ c : SynthCircuit (preparationExponent κ),
      c = preparationCompiler κ ŝ ∧
      c.workCalls = mainBudget κ ∧ c.firstCalls = mainBudget κ ∧
      c.secondCalls = reflectionBudget κ ŝ ∧
      c.auxGates ≤ 1110*mainBudget κ ∧
      c.chargedGates (preparationWorkCode a h).length ≤ 184485*(a+1)*mainBudget κ ∧
      (preparationWorkCode a h).length ≤ 183375*(a+1) ∧
      (∀ g ∈ preparationWorkCode a h, g.arity ≤ 2 ∧ Preparation.WorkGates.RealGate g) ∧
      (∀ (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ),
        (((positiveWorkMacro a n (preparationExponent κ) (preparationWorkCode a h)).toQuery
          (positiveWorkGateEval a n (preparationExponent κ) (preparationExponent_pos h))).eval UA Ub).val *
            basisInsertion (clean a n (preparationExponent κ)) =
          basisInsertion (clean a n (preparationExponent κ)) *
            (padHom (cachedWork (finitePreparationWork (D := Fin 4 × Bits n)
              (physicalSignalZero (fun _ : Fin a => false)) h
              (by have := h.kappa_pos; positivity : 0<1+κ⁻¹)))).val) ∧
      auxiliaryQubits (preparationExponent κ) ≤ 2*Nat.log2 ⌈κ⌉₊+59 ∧
      (∀ (W : Matrix.unitaryGroup (Base (PreparationData (Bits a) (Bits n))) ℂ)
        (U₁ U₂ : Matrix.unitaryGroup (PreparationData (Bits a) (Bits n)) ℂ),
        (∀ g ∈ c, g.isAuxiliary = true →
          ∀ i j, ((g.eval W U₁ U₂).val i j).im = 0) ∧
        ∀ v : BitSpace (PreparationData (Bits a) (Bits n)) (preparationExponent κ) → ℂ,
          (c.eval W U₁ U₂).val *ᵥ synthClean (TransducerCompiler.cleanVector v) =
            synthClean (TransducerCompiler.cleanVector
              ((toBitUnitary (hadamardFiniteUnitary h.layout W U₁ U₂)).val *ᵥ v))) ∧
      ∀ (t : ℝ) (h' : BudgetParameters κ t ŝ),
        (c.firstCalls : ℝ) < 256000000*κ ∧
        (c.secondCalls : ℝ) < 60000000*(κ/t) ∧
        ∀ (A : Matrix (Bits n) (Bits n) ℂ) (hA : A.IsHermitian),
          IsUnit A → ‖Ring.inverse A‖≤κ →
          ∀ (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ),
            IsBlockEncoding (fun _ : Fin a => false) 1 0 UA A →
            ∀ (Ub : Matrix.unitaryGroup (Bits n) ℂ) (b : EuclideanSpace ℂ (Bits n)),
              ‖b‖=1 → (∀ i,Ub i (fun _ => false)=b i) → t=solutionScale 1 A b →
              ‖WithLp.toLp 2
                ((c.eval
                    (finitePreparationWork (D := Fin 4 × Bits n)
                      (physicalSignalZero (fun _ : Fin a => false)) h'
                      (by have := h'.kappa_pos; positivity : 0<1+κ⁻¹))
                    (doubleOracle (physicalEncoding κ h'.kappa_pos UA))
                    (doubleOracle (signalLift (S := PhysicalSignal (Bits a))
                      (preparedReflection (signalLift (S := Fin 4) Ub) (1,fun _ : Fin n => false))))).val *ᵥ
                    synthInput h'.layout (preparationInternal (physicalSignalZero (fun _ : Fin a => false))
                      (WithLp.ofLp (graphInput b))) -
                  appendixA2IdealState (fun _ : Fin a => false) (fun _ : Fin n => false) h' A Ub b)‖ <
                (1 : ℝ)/1000 := by
  have hc := preparationCompiler_resources h
  have hg := synthesized_work_gate_bound (preparationExponent κ) 0 (preparationPeriod κ ŝ)
    (preparationWorkCode a h).length
  have hw := preparationWorkCode_length a h
  have hcharge : (preparationCompiler κ ŝ).chargedGates (preparationWorkCode a h).length ≤
      184485*(a+1)*mainBudget κ := by
    apply hg.trans
    change (1110+(preparationWorkCode a h).length)*mainBudget κ ≤ _
    apply Nat.mul_le_mul_right
    omega
  have hwork := appendixA2_controlled_work a n h
  refine ⟨preparationCompiler κ ŝ,rfl,hc.1,hc.2.1,hc.2.2.1,hc.2.2.2,hcharge,
    hwork.1,hwork.2.1,hwork.2.2,appendixA2_qubits h,?_,?_⟩
  · intro W U₁ U₂
    refine ⟨?_,?_⟩
    · intro g _ haux i j
      exact auxiliary_real g haux W U₁ U₂ i j
    · intro v
      exact complete_cleanup h.layout 0 (preparationPeriod κ ŝ)
        h.layout_D₁_dyadic h.layout_D₂_dyadic W U₁ U₂ v
  · intro t h'
    refine ⟨?_,?_,?_⟩
    · rw [hc.2.1]
      exact h'.mainBudget_bounds.2
    · rw [hc.2.2.1]
      exact h'.reflectionBudget_scale_bound
    · intro A hA hunit hinv UA henc Ub b hb hcol ht
      have he := appendixA2_original_error _ _ h' A hA hunit hinv UA henc Ub b hb hcol ht
      rw [originalPreparedState_eq _ _ h' UA Ub b hcol] at he
      exact he

/-- The same finite state, after replacing `U_H` and `R_e` by the original
oracles, is emitted by one actual real elementary list.  The added reflection
cost is explicitly `O((κ/s)(n+1))`; it is not charged to the source's `U_H/R_e`
version of A.2.  Both full oracle unitaries remain universally quantified. -/
theorem appendixA2_physical (a n : ℕ) {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ) :
    ∃ out : Preparation.CompilerAttachment.Circuit a n (preparationExponent κ),
      (out.toQuery (gateEval a n _ (preparationExponent_pos h))).matrixQueries = 2*mainBudget κ ∧
      (out.toQuery (gateEval a n _ (preparationExponent_pos h))).vectorQueries = 2*reflectionBudget κ ŝ+1 ∧
      out.workGates ≤ 436789*(a+1)*mainBudget κ+11222*(n+1)*reflectionBudget κ ŝ+2401 ∧
      (∀ g, NamedInstruction.gate g ∈ out → g.arity ≤ 2 ∧
        ∀ i j, ((gateEval a n _ (preparationExponent_pos h) g).val i j).im = 0) ∧
      (∀ p adj, NamedInstruction.matrixCall p adj ∈ out →
        p = graphSingleFlagPort a n (preparationExponent κ)) ∧
      (∀ p adj, NamedInstruction.vectorCall p adj ∈ out →
        p = sourceSingleFlagPort a n (preparationExponent κ)) ∧
      Fintype.card (Physical a n (preparationExponent κ)) =
        2^(n+a+2*preparationExponent κ+13) ∧
      n+a+2*preparationExponent κ+13 ≤ n+a+2*Nat.log2 ⌈κ⌉₊+69 ∧
      ∀ (t : ℝ) (h' : BudgetParameters κ t ŝ),
        (out.workGates : ℝ) < 200000000000000*κ*(a+1)+700000000000*(κ/t)*(n+1) ∧
        ∀ (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ),
          ((out.toQuery (gateEval a n _ (preparationExponent_pos h))).eval UA Ub).val *ᵥ
            Pi.single (allZero a n (preparationExponent κ)) 1 =
            basisInsertion (clean a n (preparationExponent κ)) *ᵥ
              originalPreparedState (fun _ : Fin a => false) (fun _ : Fin n => false) h' UA Ub ∧
          (∀ x scratch,
            (((out.toQuery (gateEval a n _ (preparationExponent_pos h))).eval UA Ub).val *ᵥ
              Pi.single (allZero a n (preparationExponent κ)) 1) (x,scratch) =
              if scratch=(false,false,false) then
                originalPreparedState (fun _ : Fin a => false) (fun _ : Fin n => false) h' UA Ub x
              else 0) ∧
          ∀ (A : Matrix (Bits n) (Bits n) ℂ) (hA : A.IsHermitian),
            IsUnit A → ‖Ring.inverse A‖≤κ →
            IsBlockEncoding (fun _ : Fin a => false) 1 0 UA A →
            ∀ b : EuclideanSpace ℂ (Bits n),
              ‖b‖=1 → (∀ i,Ub i (fun _ => false)=b i) → t=solutionScale 1 A b →
              ‖WithLp.toLp 2
                (((out.toQuery (gateEval a n _ (preparationExponent_pos h))).eval UA Ub).val *ᵥ
                    Pi.single (allZero a n (preparationExponent κ)) 1 -
                  basisInsertion (clean a n (preparationExponent κ)) *ᵥ
                    appendixA2IdealState (fun _ : Fin a => false) (fun _ : Fin n => false) h' A Ub b)‖ <
                (1 : ℝ)/1000 := by
  obtain ⟨out,hm,hv,hg,hr,hmp,hvp,he⟩ := physical_preparation_complete a n h
  have hwidth := physical_qubit_bound a n h
  refine ⟨out,hm,hv,hg,hr,hmp,hvp,hwidth.1,hwidth.2,?_⟩
  intro t h'
  obtain ⟨hg',he'⟩ := he t h'
  refine ⟨hg',?_⟩
  intro UA Ub
  refine ⟨he' UA Ub,?_,?_⟩
  · intro x scratch
    rw [he' UA Ub,Preparation.CompilerAttachment.cleanVector_apply]
  · intro A hA hunit hinv henc b hb hcol ht
    rw [he' UA Ub,Preparation.CompilerAttachment.cleanVector_sub_norm]
    exact appendixA2_original_error _ _ h' A hA hunit hinv UA henc Ub b hb hcol ht

end OptimalQLS.PaperStatements
