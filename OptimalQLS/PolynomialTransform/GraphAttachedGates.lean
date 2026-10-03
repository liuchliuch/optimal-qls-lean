import OptimalQLS.PolynomialTransform.GraphOracleWiring
import OptimalQLS.PolynomialTransform.GraphAttachmentWiring
import OptimalQLS.PolynomialTransform.CleanTransport
import OptimalQLS.PolynomialTransform.NamedCircuit

/-! # Two concrete elementary-gate families on one shared physical workspace -/
noncomputable section
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000
namespace OptimalQLS.PolynomialTransform
open Matrix DirtyAncilla
variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

/-- Only regrouping of named physical bits, including the two graph-data bits. -/
def graphAttachWiring (a : ℕ) (D : Type*) :
    GraphLocalState × ((Fin a → Bool) × D) ≃ PhysicalSignal (a+4) × (Fin 4 × D) :=
  (graphLocalWiring (Fin a → Bool) D).trans
    (maskedPhysicalWiring (a+4) (graphSignalBits a))

theorem graphAttach_clean (a : ℕ) (x : LogicalSignal (a+4) × (Fin 4 × D)) :
    graphAttachWiring a D
      (graphLocalClean ((maskSignalEquiv (D := Fin 4 × D) (a+4) (graphSignalBits a)).symm x))=
        physicalClean (a+4) x := by
  simp only [graphAttachWiring,graphLocalClean,Equiv.trans_apply,Equiv.apply_symm_apply]
  change physicalEquiv (a+4) (Fin 4 × D)
    ((maskSignalEquiv (a+4) (graphSignalBits a))
      ((maskSignalEquiv (a+4) (graphSignalBits a)).symm x),(false,false,false))=_
  rw [Equiv.apply_symm_apply]
  rfl

/-- Each constructor is an actual one- or two-qubit gate on named wires.
The graph-data bits are spectators of qsp gates and explicit wires of graph gates. -/
inductive GraphAttachedGate (a : ℕ) where
  | qsp (g : PhaseGate (QSVTWire (a+4)))
  | graph (g : PhaseGate GraphLocalWire)

def GraphAttachedGate.eval (a : ℕ) : GraphAttachedGate a →
    Matrix.unitaryGroup (PhysicalSignal (a+4) × (Fin 4 × D)) ℂ
  | .qsp g => elementaryPlacement g.eval
  | .graph g => rewireUnitary (graphAttachWiring a D) (elementaryPlacement g.eval)

def GraphAttachedGate.arity {a : ℕ} : GraphAttachedGate a → ℕ
  | .qsp g => g.arity
  | .graph g => g.arity

theorem GraphAttachedGate.arity_le_two {a : ℕ} (g : GraphAttachedGate a) : g.arity ≤ 2 := by
  cases g <;> exact PhaseGate.arity_le_two _

abbrev GraphAttachedCircuit (a : ℕ) (D B : Type*) :=
  NamedCircuit (GraphAttachedGate a) ((Fin a → Bool) × D) B (PhysicalSignal (a+4) × (Fin 4 × D))

def attachedQSPMacro (a : ℕ) (code : List (PhaseGate (QSVTWire (a+4)))) : GraphAttachedCircuit a D B :=
  code.map (fun g => .gate (.qsp g))

theorem attachedQSPMacro_toQuery (a : ℕ) (code : List (PhaseGate (QSVTWire (a+4)))) :
    (attachedQSPMacro (D := D) (B := B) a code).toQuery (GraphAttachedGate.eval a)=
      (elementaryMacro (A := (Fin a → Bool) × D) (B := B) (D := Fin 4 × D) code).toQuery := by
  induction code with
  | nil => rfl
  | cons g code ih =>
    simpa [attachedQSPMacro,NamedCircuit.toQuery,NamedInstruction.toQuery,GraphAttachedGate.eval,
      elementaryMacro,ElementaryCircuit.toQuery,ElementaryInstruction.toQuery] using
      congrArg (List.cons (.work (elementaryPlacement g.eval))) ih

theorem attachedQSPMacro_workGates (a : ℕ) (code : List (PhaseGate (QSVTWire (a+4)))) :
    (attachedQSPMacro (D := D) (B := B) a code).workGates=code.length := by
  induction code <;> simp_all [attachedQSPMacro,NamedCircuit.workGates]

def attachGraphInstruction (a : ℕ) :
    ElementaryInstruction ((Fin a → Bool) × D) B GraphLocalWire ((Fin a → Bool) × D) →
      NamedInstruction (GraphAttachedGate a) ((Fin a → Bool) × D) B (PhysicalSignal (a+4) × (Fin 4 × D))
  | .gate g => .gate (.graph g)
  | .matrixCall p b => .matrixCall ((relabelPort (graphAttachWiring a D)).comp p) b
  | .vectorCall p b => .vectorCall ((relabelPort (graphAttachWiring a D)).comp p) b

def attachGraphCircuit (a : ℕ)
    (c : ElementaryCircuit ((Fin a → Bool) × D) B GraphLocalWire ((Fin a → Bool) × D)) :
    GraphAttachedCircuit a D B := c.map (attachGraphInstruction a)

theorem attachGraphCircuit_toQuery (a : ℕ)
    (c : ElementaryCircuit ((Fin a → Bool) × D) B GraphLocalWire ((Fin a → Bool) × D)) :
    (attachGraphCircuit a c).toQuery (GraphAttachedGate.eval a)=
      c.toQuery.lift (relabelPort (graphAttachWiring a D)) := by
  induction c with
  | nil => rfl
  | cons g c ih =>
    cases g <;> simp_all [attachGraphCircuit,attachGraphInstruction,NamedCircuit.toQuery,
      NamedInstruction.toQuery,GraphAttachedGate.eval,ElementaryCircuit.toQuery,
      ElementaryInstruction.toQuery,QueryCircuit.lift,QueryInstruction.lift]

theorem attachGraphCircuit_workGates (a : ℕ)
    (c : ElementaryCircuit ((Fin a → Bool) × D) B GraphLocalWire ((Fin a → Bool) × D)) :
    (attachGraphCircuit a c).workGates=c.workGates := by
  induction c with
  | nil => rfl
  | cons g c ih =>
    cases g <;> simp_all [attachGraphCircuit,attachGraphInstruction,NamedCircuit.workGates,
      ElementaryCircuit.workGates]

theorem attachGraphCircuit_counts (a : ℕ)
    (c : ElementaryCircuit ((Fin a → Bool) × D) B GraphLocalWire ((Fin a → Bool) × D)) :
    ((attachGraphCircuit a c).toQuery (GraphAttachedGate.eval a)).matrixQueries=c.toQuery.matrixQueries ∧
    ((attachGraphCircuit a c).toQuery (GraphAttachedGate.eval a)).vectorQueries=c.toQuery.vectorQueries ∧
    (attachGraphCircuit a c).workGates=c.workGates := by
  rw [attachGraphCircuit_toQuery]
  exact ⟨(QueryCircuit.lift_counts _ _).1,(QueryCircuit.lift_counts _ _).2,attachGraphCircuit_workGates a c⟩

theorem attachGraphCircuit_eval (a : ℕ)
    (c : ElementaryCircuit ((Fin a → Bool) × D) B GraphLocalWire ((Fin a → Bool) × D))
    (UA : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    ((attachGraphCircuit a c).toQuery (GraphAttachedGate.eval a)).eval UA Ub=
      rewireUnitary (graphAttachWiring a D) (c.toQuery.eval UA Ub) := by
  rw [attachGraphCircuit_toQuery,QueryCircuit.lift_eval,relabelPort_apply]

/-- The same scratch is restored before the next QSVT macro; this transports
whole-superposition semantics, not just initialized data basis states. -/
theorem graphAttached_intertwines (a : ℕ)
    (U : Matrix.unitaryGroup (GraphLocalState × ((Fin a → Bool) × D)) ℂ)
    (V : Matrix.unitaryGroup ((Bool × Bool) ×
      (GraphEncoding.PhysicalSignal (Fin a → Bool) × (Fin 4 × D))) ℂ)
    (h : U.val*basisInsertion graphLocalClean=basisInsertion graphLocalClean*V.val) :
    (rewireUnitary (graphAttachWiring a D) U).val*basisInsertion (physicalClean (a+4))=
      basisInsertion (physicalClean (a+4))*
        (rewireUnitary (maskSignalEquiv (a+4) (graphSignalBits a)) V).val := by
  have ht := clean_intertwines_transport (graphAttachWiring a D)
    (maskSignalEquiv (a+4) (graphSignalBits a)) graphLocalClean U V h
  simpa only [graphAttach_clean] using ht

end OptimalQLS.PolynomialTransform
