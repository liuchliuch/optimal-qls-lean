import OptimalQLS.LowerBounds.Physical.SimulationAlgebra

/-! Actual controlled/adjoint oracle-call wrappers with clean scratch. -/
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
namespace OptimalQLS.LowerBounds.Physical
open Matrix PolynomialTransform
variable {D P W A B : Type*} [Fintype D] [DecidableEq D]
  [Fintype P] [DecidableEq P] [Fintype W] [DecidableEq W]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

theorem controlled_intertwines (f : D → P) (U : Matrix.unitaryGroup P ℂ)
    (V : Matrix.unitaryGroup D ℂ) (h : U.val * basisInsertion f = basisInsertion f * V.val)
    (r : ℕ) (control : Fin r → Bool) :
    (controlledUnitary r control U).val * basisInsertion (fun x : D × Fin r => (f x.1,x.2)) =
      basisInsertion (fun x : D × Fin r => (f x.1,x.2)) * (controlledUnitary r control V).val := by
  have hh (s : Fin r) : (if control s then U.val else 1) * basisInsertion f =
      basisInsertion f * (if control s then V.val else 1) := by
    cases control s
    · simp
    · exact h
  change (Matrix.blockDiagonal fun s => if control s then U.val else 1) * _ =
    _ * (Matrix.blockDiagonal fun s => if control s then V.val else 1)
  ext ⟨p,s⟩ ⟨d,t⟩
  by_cases hst : s=t
  · subst t
    simpa [Matrix.mul_apply, basisInsertion, Fintype.sum_prod_type,
      Matrix.blockDiagonal, ite_and] using congrFun (congrFun (hh s) p) d
  · simp [Matrix.mul_apply, basisInsertion, Fintype.sum_prod_type,
      Matrix.blockDiagonal, ite_and, hst]

def simulationPort (p : QueryPort D W) : QueryPort P (P × Fin p.multiplicity) where
  multiplicity := p.multiplicity
  wiring := Equiv.refl _
  control := p.control

/-- The physical scratch insertion retains the exact original query wiring. -/
def queryClean (f : D ↪ P) (p : QueryPort D W) : W ↪ (P × Fin p.multiplicity) :=
  p.wiring.symm.toEmbedding.trans (f.prodMap (Function.Embedding.refl _))

theorem queryPort_intertwines (f : D ↪ P) (p : QueryPort D W)
    (U : Matrix.unitaryGroup P ℂ) (V : Matrix.unitaryGroup D ℂ)
    (h : U.val * basisInsertion f = basisInsertion f * V.val) :
    ((simulationPort (P := P) p).apply U).val * basisInsertion (queryClean f p) =
      basisInsertion (queryClean f p) * (p.apply V).val := by
  have hh := rewire_intertwines (fun x : D × Fin p.multiplicity => (f x.1,x.2))
    (Equiv.refl (P × Fin p.multiplicity)) p.wiring
    (controlledUnitary p.multiplicity p.control U) (controlledUnitary p.multiplicity p.control V)
    (controlled_intertwines f U V h p.multiplicity p.control)
  exact hh

/-- Controlled and adjoint simulation is an actual lifted gate list. -/
def simulatedQuery (p : QueryPort D W) (adjoint : Bool) (c : QueryCircuit A B P) :
    QueryCircuit A B (P × Fin p.multiplicity) :=
  (if adjoint then c.adjoint else c).lift (simulationPort p)

theorem simulatedQuery_intertwines (f : D ↪ P) (p : QueryPort D W) (adjoint : Bool)
    (c : QueryCircuit A B P) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (V : Matrix.unitaryGroup D ℂ)
    (h : (c.eval UA Ub).val * basisInsertion f = basisInsertion f * V.val) :
    ((simulatedQuery p adjoint c).eval UA Ub).val * basisInsertion (queryClean f p) =
      basisInsertion (queryClean f p) * (p.apply (if adjoint then V⁻¹ else V)).val := by
  cases adjoint
  · rw [simulatedQuery, QueryCircuit.lift_eval]
    exact queryPort_intertwines f p _ V h
  · simp only [simulatedQuery, if_true, QueryCircuit.lift_eval, QueryCircuit.adjoint_eval]
    apply queryPort_intertwines
    simpa only [Matrix.UnitaryGroup.inv_val, Matrix.star_eq_conjTranspose] using
      adjoint_intertwines f (c.eval UA Ub) V h

theorem simulatedQuery_counts (p : QueryPort D W) (adjoint : Bool) (c : QueryCircuit A B P) :
    (simulatedQuery p adjoint c).matrixQueries = c.matrixQueries ∧
      (simulatedQuery p adjoint c).vectorQueries = c.vectorQueries := by
  cases adjoint <;> simp [simulatedQuery, (QueryCircuit.lift_counts _ _).1,
    (QueryCircuit.lift_counts _ _).2, (QueryCircuit.adjoint_counts c).1,
    (QueryCircuit.adjoint_counts c).2]

end OptimalQLS.LowerBounds.Physical
