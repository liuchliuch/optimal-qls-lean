import OptimalQLS.Refinement.UniformDefinitions

noncomputable section
namespace OptimalQLS.Refinement
open Matrix Preparation Alignment TransducerCompiler BinaryClock PolynomialTransform PhysicalPadding
open scoped Matrix.Norms.L2Operator
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 300000

/-- The filter/correction circuits and preparation code are chosen only from
classical κ,ŝ,ε and register sizes, before the supplied oracles and actual s. -/
theorem uniform_one_run (a d : ℕ) [NeZero d] {κ ŝ ε : ℝ}
    (hκ : 2≤κ) (hlo : 3/8≤ŝ) (hhi : ŝ≤5*κ/2) (hε0 : 0<ε) (hε1 : ε<1/2) :
    ∃ cf : GraphAttachedCircuit a (PhysicalData d) (PhysicalData d),
    ∃ cc : SingleFlagCircuit a (PhysicalData d) (PhysicalData d),
      ((selectedRun (a := a) (d := d) cf cc hκ hlo hhi).matrixQueries : ℝ)<
        2*mainBudget κ+840096*κ*Real.log (1/(ε/1024)) ∧
      (selectedRun (a := a) (d := d) cf cc hκ hlo hhi).vectorQueries=2*reflectionBudget κ ŝ+1 ∧
      ((cf.workGates+cc.workGates : ℕ) : ℝ)≤3341621776*κ*(a+1)*Real.log (1/(ε/1024)) ∧
      cf.CallsOnly (graphOriginalSingleFlagPort a (PhysicalData d)) ∧
      cc.CallsOnly (originalSingleFlagPort a (PhysicalData d)) ∧
      ∀ (M : Matrix (Fin d) (Fin d) ℂ), M.IsHermitian → IsUnit M → ‖Ring.inverse M‖≤κ →
      ∀ (UA : Matrix.unitaryGroup (Bits a × PhysicalData d) ℂ),
        IsBlockEncoding (fun _ : Fin a=>false) 1 0 UA (physicalMatrix M) →
      ∀ (Ub : Matrix.unitaryGroup (PhysicalData d) ℂ) (b : DataSpace d), ‖b‖=1 →
        (∀ i,Ub i 0=activeIsometry d b i) →
        BudgetParameters κ (solutionScale 1 M b) ŝ →
        let z := WithLp.toLp 2 (fun i=>
          (((selectedRun (a := a) (d := d) cf cc hκ hlo hhi).eval UA Ub).val*ᵥPi.single (selectedRunBasis a d κ) 1)
            (selectedRunAccept a d κ i))
        z≠0 ∧ ‖NormedSpace.normalize z-physicalSolution M b‖≤ε/2 ∧ 1/65536<‖z‖^2 := by
  have hη0 : 0<ε/1024 := by positivity
  have hη1 : ε/1024<1/2 := by linarith
  obtain ⟨cf,hfq,hfv,hfg,hfp,hfe⟩ := physical_kernel_filter_single_flag
    (D := PhysicalData d) (B := PhysicalData d) a hκ hη0 hη1
  obtain ⟨cc,hcq,hcv,hcg,hcp,hce⟩ := physical_correction_single_flag
    (B := PhysicalData d) (activeIndex d) a hκ hη0 hη1
  let h : BudgetParameters κ (knownScaleWitness κ ŝ) ŝ := knownScaleWitness_budget hκ hlo hhi
  have hp := originalPreparationAlgorithm_counts (fun _ : Fin a=>false) (0 : PhysicalData d) h
  refine ⟨cf,cc,?_,?_,?_,hfp,hcp,?_⟩
  · change ((fullRunProgram (originalPreparationAlgorithm _ _ h) _ _).matrixQueries : ℝ)<_
    rw [(fullRunProgram_counts _ _ _).1,hp.1]
    push_cast
    nlinarith only [hfq,hcq]
  · change (fullRunProgram (originalPreparationAlgorithm _ _ h) _ _).vectorQueries=_
    rw [(fullRunProgram_counts _ _ _).2,hp.2,hfv,hcv]
  · push_cast
    nlinarith only [hfg,hcg]
  · intro M hM hu hi UA hUA Ub b hb hcol hbgt
    have hp' : selectedPreparationCircuit (fun _ : Fin a=>false) (0 : PhysicalData d) hκ hlo hhi=
        originalPreparationAlgorithm (fun _ : Fin a=>false) (0 : PhysicalData d) hbgt :=
      originalPreparationAlgorithm_uniform_in_scale _ _ _ _
    have hf := (hfe UA Ub (physicalMatrix M) (zeroExtend_hermitian _ M hM) hUA).1
    have hc := (hce UA Ub M hM hu hUA hi).1
    have hz := fullRunProgram_physical_correctness (fun _ : Fin a=>false)
      (physicalZero (a+4)) (physicalZero a) hbgt
      (cf.toQuery (GraphAttachedGate.eval a)) (cc.toQuery (SingleFlagGate.eval a))
      M hM hu hi hε0 hε1 UA hUA Ub b hb hcol rfl hf hc
    dsimp only at hz ⊢
    simpa only [selectedRun,hp',selectedRunBasis,selectedRunAccept,accepted] using hz

end OptimalQLS.Refinement
