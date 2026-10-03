import OptimalQLS.Reduction.AdaptedInputs
import OptimalQLS.Refinement.CleanRunTransport

/-! # The actual original-oracle solver before the final data-head extraction -/
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

def cleanEmbedding (a n ℓ : ℕ) :
    PhysicalProgram.Register a (n+1) ℓ ↪ PhysicalAdapter.Space a n ℓ where
  toFun := PhysicalAdapter.clean a n ℓ
  inj' := fun _ _ he=>congrArg Prod.fst he

def circuit (I : PhysicalProgram.Implementation a (n+1) (ε := ε) h) :=
  (PhysicalAdapter.adapted I).toQuery (PhysicalAdapter.gateEval a n _
    (Preparation.CompilerAttachment.preparationExponent_pos h))

def acceptance (a n ℓ : ℕ) : Fin (2^(n+1)) ↪ PhysicalAdapter.Space a n ℓ :=
  transportedAccept (cleanEmbedding a n ℓ) (dataEmbedding a (n+1) ℓ)

def initial (a n ℓ : ℕ) : PhysicalAdapter.Space a n ℓ :=
  PhysicalAdapter.clean a n ℓ (PhysicalProgram.initial a (n+1) ℓ)

def initialIndex (a n ℓ : ℕ) := Fintype.equivFin (PhysicalAdapter.Space a n ℓ) (initial a n ℓ)

def execution (I : PhysicalProgram.Implementation a (n+1) (ε := ε) h) :=
  repeatedRun (circuit I) (acceptance a n (preparationExponent κ))
    (initial a n (preparationExponent κ)) (0 : Fin (2^(n+1)))

theorem accepted_exact (I : PhysicalProgram.Implementation a (n+1) (ε := ε) h)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    acceptedVector (circuit I) (acceptance a n (preparationExponent κ))
      (initial a n (preparationExponent κ)) UA Ub=
    outputCoordinates (n+1) (I.accepted (PhysicalAdapter.matrixOracle UA) (PhysicalAdapter.vectorOracle Ub)) := by
  calc
    _=acceptedVector (runCircuit I) (dataEmbedding a (n+1) (preparationExponent κ))
        (PhysicalProgram.initial a (n+1) (preparationExponent κ))
        (PhysicalAdapter.matrixOracle UA) (PhysicalAdapter.vectorOracle Ub) :=
      clean_circuit_accepted (cleanEmbedding a n _) _ (circuit I) UA Ub _
        (PhysicalAdapter.adapted_intertwines I UA Ub) _
    _=_ := PhysicalExecution.accepted_exact I _ _

theorem accepted_norm (I : PhysicalProgram.Implementation a (n+1) (ε := ε) h)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    ‖acceptedVector (circuit I) (acceptance a n (preparationExponent κ))
      (initial a n (preparationExponent κ)) UA Ub‖=
      ‖I.accepted (PhysicalAdapter.matrixOracle UA) (PhysicalAdapter.vectorOracle Ub)‖ := by
  rw [accepted_exact,(outputCoordinates (n+1)).norm_map]

attribute [local irreducible] Repetition.repeatProgram

theorem execution_success (I : PhysicalProgram.Implementation a (n+1) (ε := ε) h)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (hp : 1/65536<‖I.accepted (PhysicalAdapter.matrixOracle UA) (PhysicalAdapter.vectorOracle Ub)‖^2) :
    (2 : ℝ)/3<(execution I).successProbability UA Ub (basis (initialIndex a n (preparationExponent κ))) ∧
    (execution I).conditionalOutput UA Ub (basis (initialIndex a n (preparationExponent κ)))=
      pureDensity (WithLp.ofLp (outputCoordinates (n+1) (NormedSpace.normalize
        (I.accepted (PhysicalAdapter.matrixOracle UA) (PhysicalAdapter.vectorOracle Ub))))) := by
  have hp' : 1/65536<‖acceptedVector (circuit I) (acceptance a n (preparationExponent κ))
      (initial a n (preparationExponent κ)) UA Ub‖^2 := by rwa [accepted_norm]
  have hh := repeatedRun_correct (circuit I) (acceptance a n (preparationExponent κ))
    (initial a n (preparationExponent κ)) (0 : Fin (2^(n+1))) UA Ub hp'
  refine ⟨hh.1,?_⟩
  simpa only [accepted_exact,isometry_normalize] using hh.2.1

theorem query_depths (I : PhysicalProgram.Implementation a (n+1) (ε := ε) h) :
    matrixDepth (execution I)≤144000*(runCircuit I).matrixQueries ∧
      (execution I).vectorDepth≤72000*(runCircuit I).vectorQueries := by
  have hc := PhysicalAdapter.adapted_counts I
  have ha : (circuit I).matrixQueries=2*(runCircuit I).matrixQueries := hc.1
  have hb : (circuit I).vectorQueries=(runCircuit I).vectorQueries := hc.2.1
  constructor
  · have hq := repeatProgram_matrixDepth (finiteRun (circuit I))
      (finiteAccept (acceptance a n (preparationExponent κ)))
      (initialIndex a n (preparationExponent κ)) (0 : Fin (2^(n+1))) 72000
    simp only [finiteRun,reindexCircuit_matrixQueries,ha] at hq
    exact hq.trans_eq (by omega)
  · simpa only [execution,repeatedRun,finiteRun,reindexCircuit_vectorQueries,hb] using
      repeatProgram_vectorDepth (finiteRun (circuit I))
        (finiteAccept (acceptance a n (preparationExponent κ)))
        (initialIndex a n (preparationExponent κ)) (0 : Fin (2^(n+1))) 72000

theorem register_bound (I : PhysicalProgram.Implementation a (n+1) (ε := ε) h) :
    RegisterBound (2^(n+3*a+2*preparationExponent κ+31)) (execution I) := by
  rw [←PhysicalAdapter.space_card a n (preparationExponent κ)]
  exact repeatProgram_registerBound _ _ _ _ _

end OptimalQLS.Reduction.AdaptedExecution
