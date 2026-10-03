import OptimalQLS.Refinement.NamedProgram
import OptimalQLS.PolynomialTransform.SingleFlagPaperTheorems

/-! # Actual coherent matrix-only refinement and its accepting branch -/
noncomputable section
namespace OptimalQLS.Refinement
open Matrix PolynomialTransform Preparation
open scoped Matrix.Norms.L2Operator
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000
variable {P D B : Type*} [Fintype P] [DecidableEq P] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B] [Nonempty D]

/-- The unitary part of Proposition5.6 is a concrete gate/query list chosen
before either oracle or the coarse state. The final coordinate measurement is
represented by its exact accepting vector and Born probability below. -/
theorem theorem56_coherent_refinement (a : ℕ) (p₀ : P) {κ ε : ℝ}
    (hκ : 2≤κ) (hε0 : 0<ε) (hε1 : ε<1/2) :
    ∃ out : NamedRefinementCircuit a P D B,
      ((out.toQuery (RefinementGate.eval a)).matrixQueries : ℝ)<840096*κ*Real.log (1/(ε/1024)) ∧
      (out.toQuery (RefinementGate.eval a)).vectorQueries=0 ∧
      (out.workGates : ℝ)≤3341621776*κ*(a+1)*Real.log (1/(ε/1024)) ∧
      ∀ (UA : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ)
        (A : Matrix D D ℂ), A.IsHermitian → IsUnit A →
        IsBlockEncoding (fun _ : Fin a => false) 1 0 UA A → ‖Ring.inverse A‖≤κ →
        ∀ (b : EuclideanSpace ℂ D), ‖b‖=1 →
        ∀ (Ψ : P × (Fin 4 × D) → ℂ), ‖WithLp.toLp 2 Ψ‖=1 →
        (∃ β : ℝ, 1/32≤β ∧ β≤1 ∧
          Alignment.kernelProjector (GraphEncoding.graphMatrix A κ)
            (WithLp.toLp 2 (fun x => Ψ (p₀,x)))=
              β • Alignment.normalizedProjectedInput (GraphEncoding.graphMatrix A κ) (graphInput b)) →
        let z := WithLp.toLp 2 (accepted p₀ (physicalZero (a+4)) (physicalZero a)
          (((out.toQuery (RefinementGate.eval a)).eval UA Ub).val*ᵥ
            jointInput (physicalZero (a+4)) (physicalZero a) Ψ))
        let x := NormedSpace.normalize
          (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (Ring.inverse A) b)
        z≠0 ∧ ‖NormedSpace.normalize z-x‖≤ε/2 ∧ 1/65536<‖z‖^2 ∧ ‖z‖^2≤1 := by
  have heta : 0<ε/1024 := by positivity
  have heta1 : ε/1024<1/2 := by linarith
  obtain ⟨cf,hfq,hfv,hfg,hfp,hfe⟩ := lemma52_kernel_filter_single_flag (D := D) (B := B) a hκ heta heta1
  obtain ⟨cc,hcq,hcv,hcg,hcp,hce⟩ := lemma55_correction_single_flag (D := D) (B := B) a hκ heta heta1
  let out := namedRefinementProgram (P := P) a cf cc
  have hout : out.toQuery (RefinementGate.eval a)=
      refinementProgram (cf.toQuery (GraphAttachedGate.eval a)) (cc.toQuery (SingleFlagGate.eval a)) :=
    namedRefinementProgram_toQuery a cf cc
  refine ⟨out,?_,?_,?_,?_⟩
  · rw [hout,(refinementProgram_counts _ _).1,Nat.cast_add]
    nlinarith
  · rw [hout,(refinementProgram_counts _ _).2,hfv,hcv]
  · change ((namedRefinementProgram (P := P) a cf cc).workGates : ℝ)≤_
    rw [namedRefinementProgram_gates,Nat.cast_add]
    nlinarith
  · intro UA Ub A hA hunit henc hinv b hb Ψ hΨ hcoarse
    obtain ⟨β,hβ0,hβ1,hβ⟩ := hcoarse
    have hf := hfe UA Ub A hA hunit henc hinv
    have hc := hce UA Ub A hA hunit henc hinv
    have hcb := exact_block_eq hc.1
    rw [one_smul] at hcb
    let F := Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ)
      (signalBlock (physicalZero (a+4)) ((cf.toQuery (GraphAttachedGate.eval a)).eval UA Ub))
    let y := WithLp.toLp 2 (fun x => Ψ (p₀,x))
    have hy : ‖y‖≤1 := (coordinate_slice_norm_le
      ⟨fun x => (p₀,x),fun _ _ h => congrArg Prod.snd h⟩ (WithLp.toLp 2 Ψ)).trans_eq hΨ
    have herr := refinement_component_guarantee A hA hunit (norm_le_of_exact_block henc)
      hκ hinv hε0 hε1 b hb y hy hβ0 hβ1 hβ F hf.2
    have hz := refinementProgram_acceptance (cf.toQuery (GraphAttachedGate.eval a))
      (cc.toQuery (SingleFlagGate.eval a)) UA Ub p₀ (physicalZero (a+4)) (physicalZero a) Ψ
    rw [← hcb] at hz
    have hz' : WithLp.toLp 2 (accepted p₀ (physicalZero (a+4)) (physicalZero a)
        (((out.toQuery (RefinementGate.eval a)).eval UA Ub).val*ᵥ
          jointInput (physicalZero (a+4)) (physicalZero a) Ψ))=
        correctionOperator A κ (ε/1024) (graphCoordinate 2 (F y)) := by
      rw [hout,hz]
      rfl
    dsimp only
    rw [hz',Perturbation.toEuclideanCLM_inverse A hunit]
    refine ⟨herr.1,herr.2.1,herr.2.2,?_⟩
    have hp := refinementProgram_acceptance_probability_le_one
      (cf.toQuery (GraphAttachedGate.eval a)) (cc.toQuery (SingleFlagGate.eval a))
      UA Ub p₀ (physicalZero (a+4)) (physicalZero a) Ψ hΨ
    rw [← hout,hz'] at hp
    exact hp

end OptimalQLS.Refinement
