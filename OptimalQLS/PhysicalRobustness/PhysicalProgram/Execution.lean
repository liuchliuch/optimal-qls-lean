import OptimalQLS.PhysicalRobustness.PhysicalProgram.Complete
import OptimalQLS.Refinement.PhysicalExecution
import OptimalQLS.Refinement.Repetition.NoisySuccess

/-! Literal finite measurement/reset repetition of the selected noisy program.
No arithmetic budget is asserted to certify a primitive execution tree here. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open scoped Classical Matrix.Norms.L2Operator
namespace OptimalQLS.PhysicalRobustness.PhysicalProgram
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform PhysicalPadding Refinement LowerBounds Repetition
open Refinement.PhysicalProgram
open Refinement.PhysicalExecution (dataEmbedding initialIndex outputCoordinates outputCoordinates_apply)
variable {a n : ℕ} {κ ŝ ε : ℝ}

def Implementation.runCircuit (I : Implementation a n κ ŝ ε) :=
  I.circuit.toQuery (gateEval a n _ (CompilerAttachment.preparationExponent_pos I.budget))

def Implementation.execution (I : Implementation a n κ ŝ ε) :=
  Repetition.repeatProgram (finiteRun I.runCircuit)
    (finiteAccept (dataEmbedding a n (preparationExponent (2*κ))))
    (initialIndex a n (preparationExponent (2*κ))) (0 : Fin (2^n)) 600000

/-- The acceptance embedding is literally the one whose Kraus maps were proved
by the physical single-bit measurement and reset construction. -/
theorem Implementation.execution_eq_physical (I : Implementation a n κ ŝ ε) :
    I.execution=Repetition.repeatProgram (finiteRun I.runCircuit)
      (PhysicalMeasurement.acceptanceEmbedding a n (preparationExponent (2*κ)))
      (initialIndex a n (preparationExponent (2*κ))) (0 : Fin (2^n)) 600000 := by
  unfold Implementation.execution
  rw [Refinement.PhysicalExecution.acceptanceEmbedding_exact]

theorem Implementation.accepted_coordinates (I : Implementation a n κ ŝ ε)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    Refinement.acceptedVector I.runCircuit (dataEmbedding a n (preparationExponent (2*κ)))
      (initial a n (preparationExponent (2*κ))) UA Ub=
      outputCoordinates n (I.accepted UA Ub) := by
  ext i
  rw [outputCoordinates_apply]
  rfl

attribute [local irreducible] Repetition.repeatProgram

/-- The same branch is now the pure conditional output of the actual finite
600000-attempt measurement/reset program, with success strictly above 2/3. -/
theorem Implementation.execution_success (I : Implementation a n κ ŝ ε)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (hp : 1/262144<‖I.accepted UA Ub‖^2) :
    (2 : ℝ)/3<I.execution.successProbability UA Ub (Repetition.basis (initialIndex a n (preparationExponent (2*κ)))) ∧
    I.execution.conditionalOutput UA Ub (Repetition.basis (initialIndex a n (preparationExponent (2*κ))))=
      pureDensity (WithLp.ofLp (outputCoordinates n (NormedSpace.normalize (I.accepted UA Ub)))) := by
  have hp' : 1/262144<successMass (finiteRun I.runCircuit)
      (finiteAccept (dataEmbedding a n (preparationExponent (2*κ))))
      (initialIndex a n (preparationExponent (2*κ))) UA Ub := by
    rw [initialIndex,finiteRun_successMass,I.accepted_coordinates,(outputCoordinates n).norm_map]
    exact hp
  have hh := operational_repetition_600000 (finiteRun I.runCircuit)
    (finiteAccept (dataEmbedding a n (preparationExponent (2*κ))))
    (initialIndex a n (preparationExponent (2*κ))) (0 : Fin (2^n)) UA Ub hp'
  refine ⟨hh.1,?_⟩
  simpa only [Implementation.execution,initialIndex,finiteRun_normalized,I.accepted_coordinates,isometry_normalize] using hh.2.1

theorem Implementation.execution_query_depths (I : Implementation a n κ ŝ ε) :
    Repetition.matrixDepth I.execution≤600000*I.runCircuit.matrixQueries ∧
      I.execution.vectorDepth≤600000*I.runCircuit.vectorQueries := by
  constructor
  · simpa only [Implementation.execution,finiteRun,reindexCircuit_matrixQueries] using
      repeatProgram_matrixDepth (finiteRun I.runCircuit)
        (finiteAccept (dataEmbedding a n (preparationExponent (2*κ))))
        (initialIndex a n (preparationExponent (2*κ))) (0 : Fin (2^n)) 600000
  · simpa only [Implementation.execution,finiteRun,reindexCircuit_vectorQueries] using
      repeatProgram_vectorDepth (finiteRun I.runCircuit)
        (finiteAccept (dataEmbedding a n (preparationExponent (2*κ))))
        (initialIndex a n (preparationExponent (2*κ))) (0 : Fin (2^n)) 600000

theorem Implementation.execution_register_bound (I : Implementation a n κ ŝ ε) :
    RegisterBound (Fintype.card (Register a n (preparationExponent (2*κ)))) I.execution :=
  repeatProgram_registerBound _ _ _ _ _

/-- The truncated comparison remains explicit after repetition and coordinate
extraction, before any independent perturbation-stability estimate is added. -/
theorem Implementation.execution_correctness (I : Implementation a n κ ŝ ε)
    {D : Type*} [Fintype D] [DecidableEq D] (f : D ↪ Bits n)
    (A : Matrix D D ℂ) (hA : A.IsHermitian) (hunit : IsUnit A) (hAnorm : ‖A‖≤1)
    (B : Matrix (Bits n) (Bits n) ℂ) (hB : B.IsHermitian)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (henc : IsBlockEncoding (fun _ : Fin a=>false) 1 0 UA B)
    (Ub : Matrix.unitaryGroup (Bits n) ℂ) (b : EuclideanSpace ℂ D) (hb : ‖b‖=1)
    (hcol : ∀ i,Ub i (fun _ : Fin n=>false)=coordinateIsometry f b i)
    {δ : ℝ} (hδ : 0≤δ) (hinv : ‖Ring.inverse A‖≤κ)
    (hpert : ‖B-zeroExtend f A‖≤δ) (hsmall : κ*δ≤1/4)
    (hestlo : solutionScale 1 A b/2≤ŝ) (hesthi : ŝ≤2*solutionScale 1 A b)
    (hε : 0<ε) (hε1 : ε<1/2) :
    (2 : ℝ)/3<I.execution.successProbability UA Ub (Repetition.basis (initialIndex a n (preparationExponent (2*κ)))) ∧
    ∃ x : EuclideanSpace ℂ (Fin (2^n)), ‖x‖=1 ∧
      ‖x-outputCoordinates n (NormedSpace.normalize
        (highInverse (Matrix.toEuclideanCLM (n := Bits n) (𝕜 := ℂ) B)
          (matrixHermitian_symmetric B hB) δ (coordinateIsometry f b)))‖≤ε/2 ∧
      I.execution.conditionalOutput UA Ub (Repetition.basis (initialIndex a n (preparationExponent (2*κ))))=
        pureDensity (WithLp.ofLp x) := by
  have hc := I.correctness f A hA hunit hAnorm B hB UA henc Ub b hb hcol hδ hinv hpert hsmall hestlo hesthi hε hε1
  have he := I.execution_success UA Ub hc.2.2.1
  refine ⟨he.1,outputCoordinates n (NormedSpace.normalize (I.accepted UA Ub)),?_,?_,he.2⟩
  · rw [(outputCoordinates n).norm_map,NormedSpace.norm_normalize hc.1]
  · rw [isometry_norm_sub]
    exact hc.2.1

end OptimalQLS.PhysicalRobustness.PhysicalProgram
