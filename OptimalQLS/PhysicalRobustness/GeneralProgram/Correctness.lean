import OptimalQLS.PhysicalRobustness.GeneralProgram.Circuit
import OptimalQLS.PhysicalRobustness.GeneralProgram.Extraction

/-! Sharp noisy non-Hermitian correctness for the actual substituted run. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open scoped Classical Matrix.Norms.L2Operator
namespace OptimalQLS.PhysicalRobustness.GeneralProgram
open Matrix LowerBounds PhysicalPadding Reduction TransducerCompiler BinaryClock PolynomialTransform
open Refinement Refinement.PhysicalExecution Refinement.Repetition
variable {D : Type*} [Fintype D] [DecidableEq D] {a n : ℕ} {α κ δ ŝ ε : ℝ}

def rightTarget (f : D ↪ Bits n) (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (b : EuclideanSpace ℂ D) (η : ℝ) :=
  rightPart (sumOutput n (NormedSpace.normalize (truncated f UA b η)))

def solution (f : D ↪ Bits n) (A : Matrix D D ℂ) (b : EuclideanSpace ℂ D) :=
  outputCoordinates n (coordinateIsometry f
    (NormedSpace.normalize (WithLp.toLp 2 (A⁻¹*ᵥWithLp.ofLp b))))

theorem normalized_solution_sum (f : D ↪ Bits n) (hα : 0<α)
    (A : Matrix D D ℂ) (hu : IsUnit A) (b : EuclideanSpace ℂ D) :
    sumOutput n (coordinateIsometry (dilationActive f)
      (NormedSpace.normalize (Matrix.toEuclideanCLM (n := D⊕D) (𝕜 := ℂ)
        (Ring.inverse (normalizedMatrix α A)) (WithLp.toLp 2 (source (WithLp.ofLp b))))))=
    WithLp.toLp 2 (rightState (WithLp.ofLp (solution f A b))) := by
  rw [←Matrix.nonsing_inv_eq_ringInverse]
  change coordinateIsometry (extractionCoordinates n).symm.toEmbedding
    (outputCoordinates (n+1) (coordinateIsometry (dilationActive f)
      (NormedSpace.normalize (WithLp.toLp 2 ((normalizedMatrix α A)⁻¹*ᵥsource (WithLp.ofLp b))))))=_
  rw [normalized_dilation_output f hα A hu]
  exact DirectExecution.reindex_right_target _

/-- Perturbation is added after projecting two exactly right-supported targets;
there is no second normalization loss on the analytic noise term. -/
theorem target_correct (f : D ↪ Bits n) (A : Matrix D D ℂ) (hu : IsUnit A)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (henc : IsBlockEncoding (fun _ : Fin a=>false) α δ UA (zeroExtend f A))
    (b : EuclideanSpace ℂ D) (hb : ‖b‖=1) (hk : 0<κ)
    (hi : α*‖Ring.inverse A‖≤κ) (hs : κ*δ/α≤1/4) :
    truncated f UA b (δ/α)≠0 ∧ ‖rightTarget f UA b (δ/α)‖=1 ∧
      ‖rightTarget f UA b (δ/α)-solution f A b‖≤2*κ*δ/α := by
  have hb' : WithLp.toLp 2 (source (WithLp.ofLp b))≠0 := by
    intro hz
    have hnorm : ‖WithLp.toLp 2 (source (WithLp.ofLp b))‖=1 := by rwa [source_norm]
    rw [hz,norm_zero] at hnorm
    norm_num at hnorm
  have ht := physical_truncated_solution_error (dilationActive f) (normalizedMatrix α A)
    (normalizedMatrix_hermitian α A) (normalizedMatrix_isUnit henc.1 A hu)
    (noisyMatrix UA) (noisyMatrix_hermitian UA) (WithLp.toLp 2 (source (WithLp.ofLp b))) hb'
    (α := 1) (κ := κ) (δ := δ/α) (by norm_num) hk (div_nonneg henc.2.1 henc.1.le)
    (by simpa only [one_mul] using normalized_inverse_bound henc.1 A hu hi)
    (noisyMatrix_error f A UA henc) (by simpa only [div_one,mul_div_assoc] using hs)
  change truncated f UA b (δ/α)≠0 ∧ _ at ht
  refine ⟨ht.1,?_,?_⟩
  · have hn := (sumOutput n).norm_map (NormedSpace.normalize (truncated f UA b (δ/α)))
    rw [NormedSpace.norm_normalize ht.1,sum_truncated_right,rightState,sumElim_norm_right] at hn
    exact hn
  · have hd := rightPart_dist_le
      (sumOutput n (NormedSpace.normalize (truncated f UA b (δ/α))))
      (sumOutput n (coordinateIsometry (dilationActive f)
        (NormedSpace.normalize (Matrix.toEuclideanCLM (n := D⊕D) (𝕜 := ℂ)
          (Ring.inverse (normalizedMatrix α A)) (WithLp.toLp 2 (source (WithLp.ofLp b)))))))
    rw [isometry_norm_sub] at hd
    rw [normalized_solution_sum f henc.1 A hu b] at hd
    have he : rightPart (WithLp.toLp 2 (rightState (WithLp.ofLp (solution f A b))))=solution f A b := rfl
    rw [he] at hd
    exact hd.trans (by simpa only [div_one,mul_div_assoc] using ht.2)

/-- Universal promised-input guarantee for the same original-oracle list. -/
theorem accepted_correct (I : Implementation a n κ ŝ ε)
    (f : D ↪ Bits n) (A : Matrix D D ℂ) (hu : IsUnit A) (hn : ‖A‖≤α)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (henc : IsBlockEncoding (fun _ : Fin a=>false) α δ UA (zeroExtend f A))
    (Ub : Matrix.unitaryGroup (Bits n) ℂ) (b : EuclideanSpace ℂ D) (hb : ‖b‖=1)
    (hcol : ∀ i,Ub i (fun _ : Fin n=>false)=coordinateIsometry f b i)
    (hi : α*‖Ring.inverse A‖≤κ) (hs : κ*δ/α≤1/4)
    (hlo : solutionScale α A b/2≤ŝ) (hhi : ŝ≤2*solutionScale α A b)
    (hε : 0<ε) (hε1 : ε<1/2) :
    accepted I UA Ub≠0 ∧ ‖NormedSpace.normalize (accepted I UA Ub)‖=1 ∧
      ‖NormedSpace.normalize (accepted I UA Ub)-solution f A b‖≤ε+2*κ*δ/α ∧
      15/4194304<‖accepted I UA Ub‖^2 := by
  obtain ⟨hH,hHu,hHn,hHi,hδ,hpert,hsmall,hbn,hbc,hsl,hsh⟩ :=
    normalize_input f A hu hn UA henc Ub b hb hcol hi hs hlo hhi
  have hc := I.correctness (dilationActive f) (normalizedMatrix α A) hH hHu hHn
    (noisyMatrix UA) (noisyMatrix_hermitian UA) (PhysicalAdapter.matrixOracle UA)
    (noisyMatrix_encoding UA) (PhysicalAdapter.vectorOracle Ub)
    (WithLp.toLp 2 (source (WithLp.ofLp b))) hbn hbc hδ hHi hpert hsmall hsl hsh hε hε1
  have ht := target_correct f A hu UA henc b hb (by linarith [I.kappa_ge_two]) hi hs
  let z := I.accepted (PhysicalAdapter.matrixOracle UA) (PhysicalAdapter.vectorOracle Ub)
  have hm : 1/262144<‖sumOutput n z‖^2 := by rw [(sumOutput n).norm_map]; exact hc.2.2.1
  have he : ‖NormedSpace.normalize (sumOutput n z)-
      WithLp.toLp 2 (rightState (WithLp.ofLp (rightTarget f UA b (δ/α))))‖≤ε/2 := by
    rw [rightTarget,←sum_truncated_right,isometry_normalize,isometry_norm_sub]
    exact hc.2.1
  have hx := noisy_direct_extraction (sumOutput n z) (rightTarget f UA b (δ/α)) ht.2.1 hm hε hε1 he
  rw [accepted_right]
  exact ⟨hx.1,hx.2.1,(norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add hx.2.2.1 ht.2.2),hx.2.2.2⟩

attribute [local irreducible] repeatProgram

theorem execution_success (I : Implementation a n κ ŝ ε)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (hp : 15/4194304<‖accepted I UA Ub‖^2) :
    (2 : ℝ)/3<(execution I).successProbability UA Ub
      (basis (AdaptedExecution.initialIndex a n (preparationExponent (2*κ)))) ∧
    (execution I).conditionalOutput UA Ub
      (basis (AdaptedExecution.initialIndex a n (preparationExponent (2*κ))))=
      pureDensity (WithLp.ofLp (NormedSpace.normalize (accepted I UA Ub))) := by
  have hp' : 15/4194304<successMass (finiteRun (runCircuit I))
      (finiteAccept (DirectExecution.acceptance a n (preparationExponent (2*κ))))
      (AdaptedExecution.initialIndex a n (preparationExponent (2*κ))) UA Ub := by
    rw [AdaptedExecution.initialIndex,finiteRun_successMass]
    exact hp
  have hh := direct_repetition_success (finiteRun (runCircuit I))
    (finiteAccept (DirectExecution.acceptance a n (preparationExponent (2*κ))))
    (AdaptedExecution.initialIndex a n (preparationExponent (2*κ))) (0 : Fin (2^n)) UA Ub hp'
  refine ⟨hh.1,?_⟩
  simpa only [execution,AdaptedExecution.initialIndex,finiteRun_normalized,accepted] using hh.2

end OptimalQLS.PhysicalRobustness.GeneralProgram
