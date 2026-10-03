import OptimalQLS.Refinement.Repetition.Complete

/-! # Operational repetition on arbitrary explicitly indexed circuit workspaces -/
noncomputable section
namespace OptimalQLS.Refinement
open Matrix LowerBounds Repetition
open scoped Matrix.Norms.L2Operator
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 500000
variable {A B W : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype W] [DecidableEq W] {d : ℕ}

abbrev finiteRun (c : QueryCircuit A B W) := Repetition.reindexCircuit (Fintype.equivFin W) c

def finiteAccept (e : Fin d ↪ W) : Fin d ↪ Fin (Fintype.card W) :=
  Repetition.reindexEmbedding (Fintype.equivFin W) (Equiv.refl _) e

def acceptedVector (c : QueryCircuit A B W) (e : Fin d ↪ W) (zero : W)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) : EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 (fun i=>((c.eval UA Ub).val*ᵥPi.single zero 1) (e i))

theorem finiteRun_successVector (c : QueryCircuit A B W) (e : Fin d ↪ W) (zero : W)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    Repetition.successVector (finiteRun c) (finiteAccept e) (Fintype.equivFin W zero) UA Ub=
      WithLp.ofLp (acceptedVector c e zero UA Ub) := by
  ext i
  simpa [finiteRun,finiteAccept,acceptedVector,Pi.single_apply,Matrix.mulVec,dotProduct] using
    Repetition.reindex_successVector (Fintype.equivFin W) (Equiv.refl (Fin d)) e c zero UA Ub i

theorem finiteRun_successMass (c : QueryCircuit A B W) (e : Fin d ↪ W) (zero : W)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    Repetition.successMass (finiteRun c) (finiteAccept e) (Fintype.equivFin W zero) UA Ub=
      ‖acceptedVector c e zero UA Ub‖^2 := by
  rw [Repetition.successMass,finiteRun_successVector,bornMass_eq_norm_sq]

theorem finiteRun_normalized (c : QueryCircuit A B W) (e : Fin d ↪ W) (zero : W)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    Repetition.normalizedSuccessVector (finiteRun c) (finiteAccept e) (Fintype.equivFin W zero) UA Ub=
      WithLp.ofLp (NormedSpace.normalize (acceptedVector c e zero UA Ub)) := by
  rw [Repetition.normalizedSuccessVector,finiteRun_successMass,finiteRun_successVector,
    Real.sqrt_sq (norm_nonneg _)]
  ext i
  simp [NormedSpace.normalize,RCLike.real_smul_eq_coe_smul (K := ℂ)]

def repeatedRun (c : QueryCircuit A B W) (e : Fin d ↪ W) (zero : W) (out : Fin d) :=
  Repetition.repeatProgram (finiteRun c) (finiteAccept e) (Fintype.equivFin W zero) out 72000

attribute [local irreducible] Repetition.repeatProgram

theorem repeatedRun_correct (c : QueryCircuit A B W) (e : Fin d ↪ W) (zero : W) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (hp : 1/65536<‖acceptedVector c e zero UA Ub‖^2) :
    (2 : ℝ)/3<(repeatedRun c e zero out).successProbability UA Ub (basis (Fintype.equivFin W zero)) ∧
    (repeatedRun c e zero out).conditionalOutput UA Ub (basis (Fintype.equivFin W zero))=
      pureDensity (WithLp.ofLp (NormedSpace.normalize (acceptedVector c e zero UA Ub))) ∧
    Repetition.matrixDepth (repeatedRun c e zero out)≤72000*c.matrixQueries ∧
    (repeatedRun c e zero out).vectorDepth≤72000*c.vectorQueries ∧
    Repetition.RegisterBound (Fintype.card W) (repeatedRun c e zero out) := by
  have hp' : 1/65536<Repetition.successMass (finiteRun c) (finiteAccept e)
      (Fintype.equivFin W zero) UA Ub := by rwa [finiteRun_successMass]
  have h := Repetition.operational_repetition_72000 (finiteRun c) (finiteAccept e)
    (Fintype.equivFin W zero) out UA Ub hp'
  refine ⟨h.1,?_,?_,?_,h.2.2.2.2.2.2.1⟩
  · simpa only [finiteRun_normalized] using h.2.2.1
  · simpa only [finiteRun,Repetition.reindexCircuit_matrixQueries] using h.2.2.2.2.1
  · simpa only [finiteRun,Repetition.reindexCircuit_vectorQueries] using h.2.2.2.2.2.1

end OptimalQLS.Refinement
