import OptimalQLS.Reduction.AdaptedExecution

/-! # Correctness of the supplied-original-oracle execution -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open scoped Classical Matrix.Norms.L2Operator
namespace OptimalQLS.Reduction.AdaptedExecution
open Matrix TransducerCompiler BinaryClock PolynomialTransform PhysicalPadding
open Refinement Refinement.PhysicalExecution Refinement.Repetition LowerBounds
variable {a n : ℕ} {κ s ŝ ε : ℝ} {h : BudgetParameters κ s ŝ}

theorem accepted_correct (I : PhysicalProgram.Implementation a (n+1) (ε := ε) h)
    {D : Type*} [Fintype D] [DecidableEq D] [Nonempty D] (f : D ↪ Bits n)
    {α : ℝ} (A : Matrix D D ℂ) (hA : IsUnit A) (b : EuclideanSpace ℂ D) (hb : ‖b‖=1)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (henc : IsBlockEncoding (fun _ : Fin a=>false) α 0 UA (zeroExtend f A))
    (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (hcol : ∀ i,Ub i (fun _ : Fin n=>false)=coordinateIsometry f b i)
    (hi : α*‖Ring.inverse A‖≤κ)
    (hlo : 3*solutionScale α A b/8≤ŝ) (hhi : ŝ≤5*solutionScale α A b/2)
    (hε0 : 0<ε) (hε1 : ε<1/2) :
    let z:=acceptedVector (circuit I) (acceptance a n (preparationExponent κ))
      (initial a n (preparationExponent κ)) UA Ub
    ‖NormedSpace.normalize z-WithLp.toLp 2 ((rightState (WithLp.ofLp (outputCoordinates n (coordinateIsometry f
      (NormedSpace.normalize (WithLp.toLp 2 (A⁻¹*ᵥWithLp.ofLp b))))))) ∘
      (extractionCoordinates n).symm)‖≤ε/2 ∧ 1/65536<‖z‖^2 := by
  dsimp only
  obtain ⟨hAh,hAu,hAi,hAe,hbn,hbc,hp,hs⟩ :=
    active_input_normalization f A hA b hb UA henc Ub hcol h.kappa_ge_two hi hlo hhi
  have hc := I.correctness_uniform hp (dilationActive f) (normalizedMatrix α A)
    hAh hAu hAi hε0 hε1 (PhysicalAdapter.matrixOracle UA) hAe
    (PhysicalAdapter.vectorOracle Ub) (WithLp.toLp 2 (source (WithLp.ofLp b))) hbn hbc hs
  refine ⟨?_,by rw [accepted_norm]; exact hc.2.2⟩
  rw [accepted_exact,isometry_normalize (outputCoordinates (n+1))
    (I.accepted (PhysicalAdapter.matrixOracle UA) (PhysicalAdapter.vectorOracle Ub))]
  have htarget : Ring.inverse (Matrix.toEuclideanCLM (n := D⊕D) (𝕜 := ℂ)
      (normalizedMatrix α A)) (WithLp.toLp 2 (source (WithLp.ofLp b)))=
      WithLp.toLp 2 ((normalizedMatrix α A)⁻¹*ᵥsource (WithLp.ofLp b)) := by
    rw [←Perturbation.toEuclideanCLM_inverse _ hAu,←Matrix.nonsing_inv_eq_ringInverse]
    rfl
  rw [←normalized_dilation_output f henc.1 A hA (WithLp.ofLp b),isometry_norm_sub]
  simpa only [htarget] using hc.2.1

theorem execution_correct (I : PhysicalProgram.Implementation a (n+1) (ε := ε) h)
    {D : Type*} [Fintype D] [DecidableEq D] [Nonempty D] (f : D ↪ Bits n)
    {α : ℝ} (A : Matrix D D ℂ) (hA : IsUnit A) (b : EuclideanSpace ℂ D) (hb : ‖b‖=1)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (henc : IsBlockEncoding (fun _ : Fin a=>false) α 0 UA (zeroExtend f A))
    (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (hcol : ∀ i,Ub i (fun _ : Fin n=>false)=coordinateIsometry f b i)
    (hi : α*‖Ring.inverse A‖≤κ)
    (hlo : 3*solutionScale α A b/8≤ŝ) (hhi : ŝ≤5*solutionScale α A b/2)
    (hε0 : 0<ε) (hε1 : ε<1/2) :
    (2 : ℝ)/3<(execution I).successProbability UA Ub (basis (initialIndex a n (preparationExponent κ))) ∧
    ∃ x : EuclideanSpace ℂ (Fin (2^(n+1))), ‖x‖=1 ∧
      ‖x-WithLp.toLp 2 ((rightState (WithLp.ofLp (outputCoordinates n (coordinateIsometry f
        (NormedSpace.normalize (WithLp.toLp 2 (A⁻¹*ᵥWithLp.ofLp b))))))) ∘
        (extractionCoordinates n).symm)‖≤ε/2 ∧
      (execution I).conditionalOutput UA Ub (basis (initialIndex a n (preparationExponent κ)))=
        pureDensity (WithLp.ofLp x) := by
  obtain ⟨hAh,hAu,hAi,hAe,hbn,hbc,hp,hs⟩ :=
    active_input_normalization f A hA b hb UA henc Ub hcol h.kappa_ge_two hi hlo hhi
  have hc := I.correctness_uniform hp (dilationActive f) (normalizedMatrix α A)
    hAh hAu hAi hε0 hε1 (PhysicalAdapter.matrixOracle UA) hAe
    (PhysicalAdapter.vectorOracle Ub) (WithLp.toLp 2 (source (WithLp.ofLp b))) hbn hbc hs
  have he := execution_success I UA Ub hc.2.2
  refine ⟨he.1,outputCoordinates (n+1) (NormedSpace.normalize
    (I.accepted (PhysicalAdapter.matrixOracle UA) (PhysicalAdapter.vectorOracle Ub))),?_,?_,he.2⟩
  · rw [(outputCoordinates (n+1)).norm_map,NormedSpace.norm_normalize hc.1]
  · have htarget : Ring.inverse (Matrix.toEuclideanCLM (n := D⊕D) (𝕜 := ℂ)
        (normalizedMatrix α A)) (WithLp.toLp 2 (source (WithLp.ofLp b)))=
        WithLp.toLp 2 ((normalizedMatrix α A)⁻¹*ᵥsource (WithLp.ofLp b)) := by
      rw [←Perturbation.toEuclideanCLM_inverse _ hAu,←Matrix.nonsing_inv_eq_ringInverse]
      rfl
    have hn := (outputCoordinates (n+1)).norm_map
      (NormedSpace.normalize (I.accepted (PhysicalAdapter.matrixOracle UA) (PhysicalAdapter.vectorOracle Ub))-
        coordinateIsometry (dilationActive f) (NormedSpace.normalize
          (Ring.inverse (Matrix.toEuclideanCLM (n := D⊕D) (𝕜 := ℂ) (normalizedMatrix α A))
            (WithLp.toLp 2 (source (WithLp.ofLp b))))))
    rw [map_sub,htarget,normalized_dilation_output f henc.1 A hA (WithLp.ofLp b)] at hn
    exact hn.trans_le (by simpa only [htarget] using hc.2.1)

end OptimalQLS.Reduction.AdaptedExecution
