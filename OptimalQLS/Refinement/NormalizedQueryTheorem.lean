import OptimalQLS.Refinement.UniformRun
import OptimalQLS.Refinement.RunRepetition
import OptimalQLS.Refinement.RunResources

/-! # A uniform operational normalized physical solver with both query bounds -/
noncomputable section
namespace OptimalQLS.Refinement
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform PhysicalPadding LowerBounds Repetition
open scoped Matrix.Norms.L2Operator
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 500000
attribute [local irreducible] Repetition.repeatProgram

/-- The one-run program, reset branches, finite repetition, and pure accepted
output are all constructed. The physical work-gate attachment is retained in
its separate named-list theorem, rather than being assumed by this endpoint. -/
theorem normalized_physical_query_algorithm (a d : ℕ) [NeZero d] {κ ŝ ε : ℝ}
    (hκ : 2≤κ) (hlo : 3/8≤ŝ) (hhi : ŝ≤5*κ/2) (hε0 : 0<ε) (hε1 : ε<1/2) :
    ∃ (w : ℕ) (zero : Fin w)
      (program : FiniteOracleProgram (Bits a × PhysicalData d) (PhysicalData d) (physicalDimension d) w),
      (Repetition.matrixDepth program : ℝ)<79200000000000*κ*Real.log (1/ε) ∧
      Repetition.RegisterBound w program ∧
      ∀ (M : Matrix (Fin d) (Fin d) ℂ), M.IsHermitian → IsUnit M → ‖Ring.inverse M‖≤κ →
      ∀ (UA : Matrix.unitaryGroup (Bits a × PhysicalData d) ℂ),
        IsBlockEncoding (fun _ : Fin a=>false) 1 0 UA (physicalMatrix M) →
      ∀ (Ub : Matrix.unitaryGroup (PhysicalData d) ℂ) (b : DataSpace d), ‖b‖=1 →
        (∀ i,Ub i 0=activeIsometry d b i) →
        BudgetParameters κ (solutionScale 1 M b) ŝ →
        (program.vectorDepth : ℝ)<8640000072000*(κ/solutionScale 1 M b) ∧
        (2 : ℝ)/3<program.successProbability UA Ub (Repetition.basis zero) ∧
        ∃ x : EuclideanSpace ℂ (PhysicalData d), ‖x‖=1 ∧
          ‖x-physicalSolution M b‖≤ε/2 ∧
          program.conditionalOutput UA Ub (Repetition.basis zero)=pureDensity (WithLp.ofLp x) := by
  obtain ⟨cf,cc,hqa,hqb,hg,hfp,hcp,hcorrect⟩ := uniform_one_run a d hκ hlo hhi hε0 hε1
  let c := selectedRun (a := a) (d := d) cf cc hκ hlo hhi
  let e := selectedRunAccept a d κ
  let z₀ := selectedRunBasis a d κ
  let program := repeatedRun c e z₀ (0 : PhysicalData d)
  have hm : Repetition.matrixDepth program≤72000*c.matrixQueries := by
    simpa only [program,repeatedRun,finiteRun,Repetition.reindexCircuit_matrixQueries] using
      Repetition.repeatProgram_matrixDepth (finiteRun c) (finiteAccept e)
        (Fintype.equivFin (PhysicalRunSpace a d κ) z₀) (0 : PhysicalData d) 72000
  have hv : program.vectorDepth≤72000*c.vectorQueries := by
    simpa only [program,repeatedRun,finiteRun,Repetition.reindexCircuit_vectorQueries] using
      Repetition.repeatProgram_vectorDepth (finiteRun c) (finiteAccept e)
        (Fintype.equivFin (PhysicalRunSpace a d κ) z₀) (0 : PhysicalData d) 72000
  have hr : Repetition.RegisterBound (Fintype.card (PhysicalRunSpace a d κ)) program :=
    Repetition.repeatProgram_registerBound _ _ _ _ _
  have hbgt := knownScaleWitness_budget hκ hlo hhi
  have hcost := repetition_query_bounds hbgt hε0 hε1 c.matrixQueries c.vectorQueries hqa hqb
  refine ⟨Fintype.card (PhysicalRunSpace a d κ),Fintype.equivFin _ z₀,program,?_,hr,?_⟩
  · exact (show (Repetition.matrixDepth program : ℝ)≤(72000*c.matrixQueries : ℕ) by exact_mod_cast hm).trans_lt hcost.1
  · intro M hM hu hinv UA henc Ub b hb hcol hs
    have hz := hcorrect M hM hu hinv UA henc Ub b hb hcol hs
    change acceptedVector c e z₀ UA Ub≠0 ∧
      ‖NormedSpace.normalize (acceptedVector c e z₀ UA Ub)-physicalSolution M b‖≤ε/2 ∧
      1/65536<‖acceptedVector c e z₀ UA Ub‖^2 at hz
    have hout := repeatedRun_correct c e z₀ (0 : PhysicalData d) UA Ub hz.2.2
    have hcost' := (repetition_query_bounds hs hε0 hε1 c.matrixQueries c.vectorQueries hqa hqb).2
    refine ⟨(show (program.vectorDepth : ℝ)≤(72000*c.vectorQueries : ℕ) by exact_mod_cast hv).trans_lt hcost',
      hout.1,NormedSpace.normalize (acceptedVector c e z₀ UA Ub),NormedSpace.norm_normalize hz.1,
      hz.2.1,hout.2.1⟩

end OptimalQLS.Refinement
