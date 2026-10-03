import OptimalQLS.Reduction.AdaptedCorrectness
import OptimalQLS.Reduction.DirectExtraction

/-! # Joint auxiliary/head acceptance for the actual original-oracle program -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open scoped Classical Matrix.Norms.L2Operator
namespace OptimalQLS.Reduction.DirectExecution
open Matrix TransducerCompiler BinaryClock PolynomialTransform PhysicalPadding
open Refinement Refinement.PhysicalExecution Refinement.Repetition LowerBounds
variable {a n : ℕ} {κ s ŝ ε : ℝ} {h : BudgetParameters κ s ŝ}

theorem coordinate_equiv_apply {P Q : Type*} [Fintype P] [DecidableEq P]
    [Fintype Q] [DecidableEq Q] (e : P ≃ Q) (v : EuclideanSpace ℂ P) (q : Q) :
    coordinateIsometry e.toEmbedding v q=v (e.symm q) := by
  have hh := insertion_mulVec_active e.toEmbedding (WithLp.ofLp v) (e.symm q)
  simpa only [Equiv.toEmbedding_apply,Equiv.apply_symm_apply] using hh

def acceptance (a n ℓ : ℕ) : Fin (2^n) ↪ PhysicalAdapter.Space a n ℓ :=
  (extractRightEmbedding (extractionCoordinates n)).trans (AdaptedExecution.acceptance a n ℓ)

def accepted (I : PhysicalProgram.Implementation a (n+1) (ε := ε) h)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :=
  acceptedVector (AdaptedExecution.circuit I) (acceptance a n (preparationExponent κ))
    (AdaptedExecution.initial a n (preparationExponent κ)) UA Ub

def sumAccepted (I : PhysicalProgram.Implementation a (n+1) (ε := ε) h)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :=
  coordinateIsometry (extractionCoordinates n).symm.toEmbedding
    (acceptedVector (AdaptedExecution.circuit I) (AdaptedExecution.acceptance a n (preparationExponent κ))
      (AdaptedExecution.initial a n (preparationExponent κ)) UA Ub)

theorem accepted_right (I : PhysicalProgram.Implementation a (n+1) (ε := ε) h)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    accepted I UA Ub=rightPart (sumAccepted I UA Ub) := by
  ext i
  change _=sumAccepted I UA Ub (.inr i)
  rw [sumAccepted,coordinate_equiv_apply]
  rfl

theorem reindex_right_target (x : EuclideanSpace ℂ (Fin (2^n))) :
    coordinateIsometry (extractionCoordinates n).symm.toEmbedding
      (WithLp.toLp 2 ((rightState (WithLp.ofLp x)) ∘ (extractionCoordinates n).symm))=
      WithLp.toLp 2 (rightState (WithLp.ofLp x)) := by
  ext i
  rw [coordinate_equiv_apply]
  simp

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
    accepted I UA Ub≠0 ∧ ‖NormedSpace.normalize (accepted I UA Ub)‖=1 ∧
      ‖NormedSpace.normalize (accepted I UA Ub)-outputCoordinates n (coordinateIsometry f
        (NormedSpace.normalize (WithLp.toLp 2 (A⁻¹*ᵥWithLp.ofLp b))))‖≤ε ∧
      1/262144<‖accepted I UA Ub‖^2 := by
  have hc := AdaptedExecution.accepted_correct I f A hA b hb UA henc Ub hcol hi hlo hhi hε0 hε1
  let x:=outputCoordinates n (coordinateIsometry f
    (NormedSpace.normalize (WithLp.toLp 2 (A⁻¹*ᵥWithLp.ofLp b))))
  have hx : ‖x‖=1 := by
    rw [(outputCoordinates n).norm_map,(coordinateIsometry f).norm_map]
    exact normalized_original_solution_unit A hA (WithLp.ofLp b) hb
  have hm : 1/65536<‖sumAccepted I UA Ub‖^2 := by
    simpa only [sumAccepted,LinearIsometry.norm_map] using hc.2
  have he : ‖NormedSpace.normalize (sumAccepted I UA Ub)-WithLp.toLp 2 (rightState (WithLp.ofLp x))‖≤ε/2 := by
    rw [sumAccepted,isometry_normalize (coordinateIsometry (extractionCoordinates n).symm.toEmbedding),
      ←reindex_right_target x,isometry_norm_sub]
    exact hc.1
  rw [accepted_right]
  exact direct_extraction_guarantee _ x hx hm hε0 hε1 he

def execution (I : PhysicalProgram.Implementation a (n+1) (ε := ε) h) :=
  repeatProgram (finiteRun (AdaptedExecution.circuit I))
    (finiteAccept (acceptance a n (preparationExponent κ)))
    (AdaptedExecution.initialIndex a n (preparationExponent κ)) (0 : Fin (2^n)) 600000

attribute [local irreducible] repeatProgram

theorem execution_success (I : PhysicalProgram.Implementation a (n+1) (ε := ε) h)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (hp : 1/262144<‖accepted I UA Ub‖^2) :
    (2 : ℝ)/3<(execution I).successProbability UA Ub (basis (AdaptedExecution.initialIndex a n (preparationExponent κ))) ∧
    (execution I).conditionalOutput UA Ub (basis (AdaptedExecution.initialIndex a n (preparationExponent κ)))=
      pureDensity (WithLp.ofLp (NormedSpace.normalize (accepted I UA Ub))) := by
  have hp' : 1/262144<successMass (finiteRun (AdaptedExecution.circuit I))
      (finiteAccept (acceptance a n (preparationExponent κ)))
      (AdaptedExecution.initialIndex a n (preparationExponent κ)) UA Ub := by
    rw [AdaptedExecution.initialIndex,finiteRun_successMass]
    exact hp
  have hh := operational_repetition_600000 (finiteRun (AdaptedExecution.circuit I))
    (finiteAccept (acceptance a n (preparationExponent κ)))
    (AdaptedExecution.initialIndex a n (preparationExponent κ)) (0 : Fin (2^n)) UA Ub hp'
  refine ⟨hh.1,?_⟩
  simpa only [execution,AdaptedExecution.initialIndex,finiteRun_normalized,accepted] using hh.2.1

end OptimalQLS.Reduction.DirectExecution
