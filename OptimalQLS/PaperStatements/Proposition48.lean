import OptimalQLS.Preparation.OriginalState
import OptimalQLS.Preparation.CompilerAttachment.WorkGates

/-! Proposition 4.8 with the original graph/input promises, the canonical
catalyst, and the literal controlled work word of that same transducer. -/
noncomputable section
namespace OptimalQLS.PaperStatements
open Matrix TransducerCompiler BinaryClock PolynomialTransform GraphEncoding
open Preparation Preparation.CompilerAttachment
open scoped Matrix.Norms.L2Operator
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1000000

/-- No transduction or catalyst-cost premise is supplied: all three costs and
the exact relation are derived from the normalized original QLS instance. -/
theorem proposition48 (a n : ℕ) {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ) :
    let hα : 0 < 1+κ⁻¹ := by have := h.kappa_pos; positivity
    let s₀ := physicalSignalZero (fun _ : Fin a => false)
    let W := finitePreparationWork (D := Fin 4 × Bits n) s₀ h hα
    let code := preparationWorkCode a h
    code.length ≤ 183375*(a+1) ∧
    (∀ g ∈ code, g.arity ≤ 2 ∧ Preparation.WorkGates.RealGate g) ∧
    (∀ (ℓ : ℕ) (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ),
      (((workMacro a n ℓ code).toQuery (workGateEval a n ℓ)).eval UA Ub).val *
        basisInsertion (clean a n (ℓ+1)) =
        basisInsertion (clean a n (ℓ+1)) * (padHom (cachedWork W)).val) ∧
    ∀ (A : Matrix (Bits n) (Bits n) ℂ) (hA : A.IsHermitian), IsUnit A → ‖Ring.inverse A‖ ≤ κ →
      ∀ (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ),
        IsBlockEncoding (fun _ : Fin a => false) 1 0 UA A →
        ∀ (Ub : Matrix.unitaryGroup (Bits n) ℂ) (b : EuclideanSpace ℂ (Bits n)),
          ‖b‖ = 1 → (∀ i, Ub i (fun _ : Fin n => false) = b i) → s = solutionScale 1 A b →
          let H := graphMatrix A κ
          let hH := graphMatrix_hermitian A hA κ
          let V := physicalEncoding κ h.kappa_pos UA
          let R := preparedReflection (signalLift (S := Fin 4) Ub) (1,fun _ : Fin n => false)
          let e := WithLp.ofLp (graphInput b)
          let q := preparationQ H R (overlapMixingParameter κ ŝ) e
          let ψ := preparationOutput H R (overlapMixingParameter κ ŝ) e
          let ω₀ := preparationInternal s₀ q
          let ωH := preparationFirst s₀ V H hH (1+κ⁻¹) ŝ q
          let ωe := preparationSecond s₀ H q
          W.val *ᵥ bundle (preparationInternal s₀ e) ω₀
            ((doubleOracle V).val *ᵥ ωH)
            ((doubleOracle (signalLift (S := GraphEncoding.PhysicalSignal (Bits a)) R)).val *ᵥ ωe) =
              bundle (preparationInternal s₀ ψ) ω₀ ωH ωe ∧
          ‖WithLp.toLp 2 ψ‖ = 1 ∧
          (inner ℂ (Alignment.normalizedProjectedInput H (graphInput b)) (WithLp.toLp 2 ψ)).im = 0 ∧
          1/30 < (inner ℂ (Alignment.normalizedProjectedInput H (graphInput b)) (WithLp.toLp 2 ψ)).re ∧
          energy ωH < 8*κ ∧ energy ωe ≤ κ/(8*ŝ) ∧ κ/(8*ŝ) ≤ κ/(3*s) ∧
          energy ω₀ + energy ωH + energy ωe < 9*κ := by
  dsimp only
  have hα : 0 < 1+κ⁻¹ := by have := h.kappa_pos; positivity
  refine ⟨preparationWorkCode_length a h, ?_, ?_, ?_⟩
  · intro g hg
    exact ⟨DirtyAncilla.PhaseGate.arity_le_two g, compiledWorkProgram_real (a+4) _ _ true g hg⟩
  · intro ℓ UA Ub
    exact workMacro_intertwines a n ℓ h UA Ub
  · intro A hA hunit hinv UA henc Ub b hb hcol hs
    have hα2 : 1+κ⁻¹ ≤ 2 := by
      have hi : κ⁻¹ ≤ 1 := by
        rw [inv_eq_one_div]
        apply (div_le_iff₀ h.kappa_pos).mpr
        linarith [h.kappa_ge_two]
      linarith
    have hblock := exact_block_eq (physicalEncoding_exact κ h.kappa_pos
      (fun _ : Fin a => false) UA A hA henc)
    have hInv : ‖Ring.inverse (Matrix.toEuclideanCLM (n := Bits n) (𝕜 := ℂ) A)‖ ≤ κ := by
      rw [← Perturbation.toEuclideanCLM_inverse A hunit]
      exact hinv
    have hp := graphInput_promises A hA
      (hunit.map (Matrix.toEuclideanCLM (n := Bits n) (𝕜 := ℂ)).toMonoidHom) h.kappa_pos
      (norm_le_of_exact_block henc) hInv b hb
    have hscale : ‖Ring.inverse (Matrix.toEuclideanCLM (n := Bits n) (𝕜 := ℂ) A) b‖ = s := by
      rw [← Perturbation.toEuclideanCLM_inverse A hunit]
      simpa only [solutionScale, one_mul] using hs.symm
    dsimp only at hp
    rw [hscale] at hp
    have hc := canonical_energy_bounds (physicalSignalZero (fun _ : Fin a => false))
      (physicalEncoding κ h.kappa_pos UA) (physicalEncoding_hermitian κ h.kappa_pos UA)
      (graphMatrix A κ) (graphMatrix_hermitian A hA κ)
      (signalLift (S := Fin 4) Ub) (1,fun _ : Fin n => false) (graphInput b)
      hp.1 (graphInput_source Ub _ b hcol) h.kappa_ge_two h.scale_ge_one h.scale_le_kappa
      h.estimate_lower h.estimate_upper hα hα2 hblock hp.2.1 hp.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2
    have hi := ideal_matrix_guarantees (graphMatrix A κ) (signalLift (S := Fin 4) Ub)
      (1,fun _ : Fin n => false) (graphInput b) hp.1 (graphInput_source Ub _ b hcol)
      h.kappa_ge_two h.scale_ge_one h.scale_le_kappa h.estimate_lower h.estimate_upper
      hp.2.1 hp.2.2.1 hp.2.2.2.2.1
    dsimp only at hc hi ⊢
    refine ⟨canonical_relation _ _ (physicalEncoding_hermitian κ h.kappa_pos UA)
      _ (graphMatrix_hermitian A hA κ) _ hα h.estimate_pos (preparation_mix_abs h) hblock _,
      hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hc.1, hc.2.2, hi.2.2.2.2.2.2.2, hc.2.1⟩

end OptimalQLS.PaperStatements
