import OptimalQLS.Refinement.PhysicalProgram.Reparameterize
import OptimalQLS.Refinement.PhysicalMeasurement
import OptimalQLS.Refinement.RunRepetition
import OptimalQLS.Refinement.RunResources

/-! # Literal physical-run repetition and its actual accepted output -/
noncomputable section
namespace OptimalQLS.Refinement.PhysicalExecution
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform PhysicalPadding LowerBounds Repetition
open scoped Matrix.Norms.L2Operator
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
variable {a n : ℕ} {κ s ŝ ε : ℝ} {h : BudgetParameters κ s ŝ}

/-- Ordinary low-first binary data coordinates, preserving the actual amplitudes. -/
def outputCoordinates (n : ℕ) : EuclideanSpace ℂ (Bits n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (2^n)) :=
  coordinateIsometry (HadamardClock.bitsFinEquiv n).toEmbedding

theorem outputCoordinates_apply (n : ℕ) (v : EuclideanSpace ℂ (Bits n)) (i : Fin (2^n)) :
    outputCoordinates n v i=v ((HadamardClock.bitsFinEquiv n).symm i) := by
  have he (j : Bits n) : i=HadamardClock.bitsFinEquiv n j ↔ (HadamardClock.bitsFinEquiv n).symm i=j := by
    constructor
    · intro h; simpa using congrArg (HadamardClock.bitsFinEquiv n).symm h
    · intro h; simpa using congrArg (HadamardClock.bitsFinEquiv n) h
  simp [outputCoordinates,coordinateIsometry_apply,insertion,basisInsertion,Matrix.mulVec,dotProduct,he]

def dataEmbedding (a n ℓ : ℕ) : Fin (2^n) ↪ PhysicalProgram.Register a n ℓ where
  toFun i := PhysicalMeasurement.dataIndex a n ℓ ((HadamardClock.bitsFinEquiv n).symm i)
  inj' := by
    intro i j he
    have hi := congrArg (fun p=>p.2.2.2.2) he
    exact (HadamardClock.bitsFinEquiv n).symm.injective hi

def runCircuit (I : PhysicalProgram.Implementation a n (ε := ε) h) :=
  I.circuit.toQuery (PhysicalProgram.gateEval a n _ (CompilerAttachment.preparationExponent_pos h))

def execution (I : PhysicalProgram.Implementation a n (ε := ε) h) :=
  repeatedRun (runCircuit I) (dataEmbedding a n (preparationExponent κ))
    (PhysicalProgram.initial a n (preparationExponent κ)) (0 : Fin (2^n))

def initialIndex (a n ℓ : ℕ) : Fin (Fintype.card (PhysicalProgram.Register a n ℓ)) :=
  Fintype.equivFin _ (PhysicalProgram.initial a n ℓ)

theorem acceptanceEmbedding_exact (a n ℓ : ℕ) :
    finiteAccept (dataEmbedding a n ℓ)=PhysicalMeasurement.acceptanceEmbedding a n ℓ := by
  ext i
  rw [PhysicalMeasurement.acceptanceEmbedding_apply]
  rfl

theorem accepted_exact (I : PhysicalProgram.Implementation a n (ε := ε) h)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    acceptedVector (runCircuit I) (dataEmbedding a n (preparationExponent κ))
      (PhysicalProgram.initial a n (preparationExponent κ)) UA Ub=
    outputCoordinates n (I.accepted UA Ub) := by
  ext i
  rw [outputCoordinates_apply]
  rfl

theorem accepted_norm (I : PhysicalProgram.Implementation a n (ε := ε) h)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    ‖acceptedVector (runCircuit I) (dataEmbedding a n (preparationExponent κ))
      (PhysicalProgram.initial a n (preparationExponent κ)) UA Ub‖=‖I.accepted UA Ub‖ := by
  rw [accepted_exact,(outputCoordinates n).norm_map]

attribute [local irreducible] Repetition.repeatProgram

/-- The semantic finite program measures exactly the same auxiliary pattern as
PhysicalMeasurement's proved one-bit realization. -/
theorem execution_success (I : PhysicalProgram.Implementation a n (ε := ε) h)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (hp : 1/65536<‖I.accepted UA Ub‖^2) :
    (2 : ℝ)/3<(execution I).successProbability UA Ub (Repetition.basis (initialIndex a n (preparationExponent κ))) ∧
    (execution I).conditionalOutput UA Ub (Repetition.basis (initialIndex a n (preparationExponent κ)))=
      pureDensity (WithLp.ofLp (outputCoordinates n (NormedSpace.normalize (I.accepted UA Ub)))) := by
  have hp' : 1/65536<‖acceptedVector (runCircuit I) (dataEmbedding a n (preparationExponent κ))
      (PhysicalProgram.initial a n (preparationExponent κ)) UA Ub‖^2 := by rwa [accepted_norm]
  have hh := repeatedRun_correct (runCircuit I) (dataEmbedding a n (preparationExponent κ))
    (PhysicalProgram.initial a n (preparationExponent κ)) (0 : Fin (2^n)) UA Ub hp'
  refine ⟨hh.1,?_⟩
  simpa only [accepted_exact,isometry_normalize] using hh.2.1

theorem execution_query_depths (I : PhysicalProgram.Implementation a n (ε := ε) h) :
    Repetition.matrixDepth (execution I)≤72000*(runCircuit I).matrixQueries ∧
      (execution I).vectorDepth≤72000*(runCircuit I).vectorQueries := by
  constructor
  · simpa only [execution,repeatedRun,finiteRun,reindexCircuit_matrixQueries] using
      repeatProgram_matrixDepth (finiteRun (runCircuit I)) (finiteAccept (dataEmbedding a n (preparationExponent κ)))
        (initialIndex a n (preparationExponent κ)) (0 : Fin (2^n)) 72000
  · simpa only [execution,repeatedRun,finiteRun,reindexCircuit_vectorQueries] using
      repeatProgram_vectorDepth (finiteRun (runCircuit I)) (finiteAccept (dataEmbedding a n (preparationExponent κ)))
        (initialIndex a n (preparationExponent κ)) (0 : Fin (2^n)) 72000

theorem execution_register_bound (I : PhysicalProgram.Implementation a n (ε := ε) h) :
    RegisterBound (Fintype.card (PhysicalProgram.Register a n (preparationExponent κ))) (execution I) :=
  repeatProgram_registerBound _ _ _ _ _

/-- Real execution error and success for each admissible hidden scale, with
one actual circuit selected before all active-coordinate embeddings. -/
theorem execution_correct (I : PhysicalProgram.Implementation a n (ε := ε) h)
    {t : ℝ} (h' : BudgetParameters κ t ŝ) {D : Type*} [Fintype D] [DecidableEq D]
    (f : D ↪ Bits n) (A : Matrix D D ℂ) (hA : A.IsHermitian) (hunit : IsUnit A)
    (hinv : ‖Ring.inverse A‖≤κ) (hε0 : 0<ε) (hε1 : ε<1/2)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ)
    (henc : IsBlockEncoding (fun _ : Fin a=>false) 1 0 UA (zeroExtend f A))
    (Ub : Matrix.unitaryGroup (Bits n) ℂ) (b : EuclideanSpace ℂ D) (hb : ‖b‖=1)
    (hcol : ∀ i,Ub i (fun _ : Fin n=>false)=coordinateIsometry f b i)
    (ht : t=solutionScale 1 A b) :
    (2 : ℝ)/3<(execution I).successProbability UA Ub (Repetition.basis (initialIndex a n (preparationExponent κ))) ∧
    ∃ x : EuclideanSpace ℂ (Fin (2^n)), ‖x‖=1 ∧
      ‖x-outputCoordinates n (coordinateIsometry f
        (NormedSpace.normalize (Ring.inverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) b)))‖≤ε/2 ∧
      (execution I).conditionalOutput UA Ub (Repetition.basis (initialIndex a n (preparationExponent κ)))=
        pureDensity (WithLp.ofLp x) := by
  have hc := I.correctness_uniform h' f A hA hunit hinv hε0 hε1 UA henc Ub b hb hcol ht
  have he := execution_success I UA Ub hc.2.2
  refine ⟨he.1,outputCoordinates n (NormedSpace.normalize (I.accepted UA Ub)),?_,?_,he.2⟩
  · rw [(outputCoordinates n).norm_map,NormedSpace.norm_normalize hc.1]
  · rw [isometry_norm_sub]
    exact hc.2.1

end OptimalQLS.Refinement.PhysicalExecution
