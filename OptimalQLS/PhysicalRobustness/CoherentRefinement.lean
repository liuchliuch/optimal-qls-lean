import OptimalQLS.PhysicalRobustness.Refinement
import OptimalQLS.PhysicalPadding.Filter
import OptimalQLS.Refinement.NamedProgram

/-! Actual matrix-only noisy refinement circuit and Born accepting branch. -/
noncomputable section
namespace OptimalQLS.PhysicalRobustness
open Matrix PolynomialTransform Preparation PhysicalPadding Refinement
open scoped Matrix.Norms.L2Operator
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000
variable {L P D W : Type*} [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P]
  [Fintype D] [DecidableEq D] [Fintype W] [DecidableEq W] [Nonempty D]

theorem noisy_coherent_refinement (a : ℕ) (p₀ : P) {κ ε : ℝ}
    (hκ : 2≤κ) (hε : 0<ε) (hε1 : ε<1/2) :
    ∃ (cf : GraphAttachedCircuit a D W) (cc : SingleFlagCircuit a D W),
      (((cf.toQuery (GraphAttachedGate.eval a)).matrixQueries : ℝ)<192*κ*Real.log (1/(ε/4096)) ∧
        (cf.toQuery (GraphAttachedGate.eval a)).vectorQueries=0 ∧
        (cf.workGates : ℝ)≤27051856*κ*(a+1)*Real.log (1/(ε/4096)) ∧
        cf.CallsOnly (graphOriginalSingleFlagPort a D)) ∧
      (((cc.toQuery (SingleFlagGate.eval a)).matrixQueries : ℝ)≤34004000000*κ*Real.log (1/(ε/4096)) ∧
        (cc.toQuery (SingleFlagGate.eval a)).vectorQueries=0 ∧
        (cc.workGates : ℝ)≤150000000000000*κ*(a+1)*Real.log (1/(ε/4096)) ∧
        cc.CallsOnly (originalSingleFlagPort a D)) ∧
      (∀ (UA : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup W ℂ)
        (B : Matrix D D ℂ), B.IsHermitian → IsBlockEncoding (fun _ : Fin a => false) 1 0 UA B →
        IsBlockEncoding (physicalZero (a+4)) 1 0 ((cf.toQuery (GraphAttachedGate.eval a)).eval UA Ub)
          (Polynomial.aeval (GraphEncoding.normalizedGraph B (2*κ))
            (liftReal (kernelFilter (graphFilterGap (2*κ)) (ε/4096)))) ∧
        IsBlockEncoding (physicalZero a) 1 0 ((cc.toQuery (SingleFlagGate.eval a)).eval UA Ub)
          (Polynomial.aeval B (liftReal (noisyCorrectionPolynomial κ (ε/4096))))) ∧
      let out := namedRefinementProgram (P := P) a cf cc
      out.toQuery (RefinementGate.eval a)=
        refinementProgram (cf.toQuery (GraphAttachedGate.eval a)) (cc.toQuery (SingleFlagGate.eval a)) ∧
      ((out.toQuery (RefinementGate.eval a)).matrixQueries : ℝ)<34004000192*κ*Real.log (1/(ε/4096)) ∧
      (out.toQuery (RefinementGate.eval a)).vectorQueries=0 ∧
      (out.workGates : ℝ)≤150000100000000*κ*(a+1)*Real.log (1/(ε/4096)) ∧
      ∀ (UA : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup W ℂ)
        (f : L ↪ D) (A : Matrix L L ℂ) (B : Matrix D D ℂ),
        A.IsHermitian → IsUnit A → ‖A‖≤1 → ∀ hB : B.IsHermitian,
        IsBlockEncoding (fun _ : Fin a => false) 1 0 UA B → ‖Ring.inverse A‖≤κ →
        ∀ (b : EuclideanSpace ℂ L), ‖b‖=1 →
        ∀ (δ ŝ : ℝ), 0≤δ → ‖B-zeroExtend f A‖≤δ → κ*δ≤1/4 →
        solutionScale 1 A b/2≤ŝ → ŝ≤2*solutionScale 1 A b →
        ∀ (Ψ : P × (Fin 4 × D) → ℂ), ‖WithLp.toLp 2 Ψ‖=1 →
        (∃ β : ℝ, 1/32≤β ∧ β≤1 ∧
          Alignment.kernelProjector (GraphEncoding.graphMatrix B (2*κ))
            (WithLp.toLp 2 (fun x => Ψ (p₀,x)))=
              β • Alignment.normalizedProjectedInput (GraphEncoding.graphMatrix B (2*κ))
                (graphInput (coordinateIsometry f b))) →
        let z := WithLp.toLp 2 (accepted p₀ (physicalZero (a+4)) (physicalZero a)
          (((out.toQuery (RefinementGate.eval a)).eval UA Ub).val*ᵥ
            jointInput (physicalZero (a+4)) (physicalZero a) Ψ))
        let v := highInverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) B)
          (matrixHermitian_symmetric B hB) δ (coordinateIsometry f b)
        z≠0 ∧ ‖NormedSpace.normalize z-NormedSpace.normalize v‖≤ε/2 ∧
          1/262144<‖z‖^2 ∧ ‖z‖^2≤1 := by
  have heta : 0<ε/4096 := by positivity
  have heta1 : ε/4096<1/2 := by linarith
  obtain ⟨cf,hfq,hfv,hfg,hfp,hfe⟩ := physical_kernel_filter_single_flag (D := D) (B := W) a
    (κ := 2*κ) (by linarith) heta heta1
  obtain ⟨cc,hcq,hcv,hcg,hcp,hce⟩ := noisyCorrection_single_flag (D := D) (W := W) a hκ heta heta1
  let out := namedRefinementProgram (P := P) a cf cc
  have hout : out.toQuery (RefinementGate.eval a)=
      refinementProgram (cf.toQuery (GraphAttachedGate.eval a)) (cc.toQuery (SingleFlagGate.eval a)) :=
    namedRefinementProgram_toQuery a cf cc
  refine ⟨cf,cc,⟨by nlinarith,hfv,by nlinarith,hfp⟩,⟨hcq,hcv,hcg,hcp⟩,?_,?_⟩
  · intro UA Ub B hB henc
    exact ⟨(hfe UA Ub B hB henc).1,hce UA Ub B hB henc⟩
  change out.toQuery (RefinementGate.eval a)=_ ∧ _
  refine ⟨hout,?_,?_,?_,?_⟩
  · rw [hout,(refinementProgram_counts _ _).1,Nat.cast_add]
    nlinarith
  · rw [hout,(refinementProgram_counts _ _).2,hfv,hcv]
  · change ((namedRefinementProgram (P := P) a cf cc).workGates : ℝ)≤_
    rw [namedRefinementProgram_gates,Nat.cast_add]
    nlinarith
  · intro UA Ub f A B hA hunit hAn hB henc hinv b hb δ ŝ hδ hpert hsmall hlo hhi Ψ hΨ hcoarse
    obtain ⟨β,hβ0,hβ1,hβ⟩ := hcoarse
    have hf := hfe UA Ub B hB henc
    have hc := hce UA Ub B hB henc
    have hcb := exact_block_eq hc
    rw [one_smul] at hcb
    let F := Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ)
      (signalBlock (physicalZero (a+4)) ((cf.toQuery (GraphAttachedGate.eval a)).eval UA Ub))
    let y := WithLp.toLp 2 (fun x => Ψ (p₀,x))
    have hy : ‖y‖≤1 := (coordinate_slice_norm_le
      ⟨fun x => (p₀,x),fun _ _ h => congrArg Prod.snd h⟩ (WithLp.toLp 2 Ψ)).trans_eq hΨ
    have herr := noisy_refinement_component_guarantee f A hA hunit hAn B hB
      (norm_le_of_exact_block henc) b hb hκ hδ hinv hpert hsmall hlo hhi hε hε1
      y hy hβ0 hβ1 hβ F hf.2
    have hz := refinementProgram_acceptance (cf.toQuery (GraphAttachedGate.eval a))
      (cc.toQuery (SingleFlagGate.eval a)) UA Ub p₀ (physicalZero (a+4)) (physicalZero a) Ψ
    rw [← hcb] at hz
    have hz' : WithLp.toLp 2 (accepted p₀ (physicalZero (a+4)) (physicalZero a)
        (((out.toQuery (RefinementGate.eval a)).eval UA Ub).val*ᵥ
          jointInput (physicalZero (a+4)) (physicalZero a) Ψ))=
        noisyCorrectionOperator B κ (ε/4096) (graphCoordinate 2 (F y)) := by
      rw [hout,hz]
      change Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)
        (Polynomial.aeval B (liftReal (noisyCorrectionPolynomial κ (ε/4096))))
        (graphCoordinate 2 (F y)) = _
      rw [polynomial_matrix_to_operator]
      rfl
    dsimp only
    rw [hz']
    refine ⟨herr.1,herr.2.1,herr.2.2,?_⟩
    have hp := refinementProgram_acceptance_probability_le_one
      (cf.toQuery (GraphAttachedGate.eval a)) (cc.toQuery (SingleFlagGate.eval a))
      UA Ub p₀ (physicalZero (a+4)) (physicalZero a) Ψ hΨ
    rw [← hout,hz'] at hp
    exact hp

end OptimalQLS.PhysicalRobustness
