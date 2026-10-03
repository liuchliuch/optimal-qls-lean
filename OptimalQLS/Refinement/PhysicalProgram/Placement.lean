import OptimalQLS.Refinement.PhysicalProgram.Frames

/-! # Structural placement of literal named-gate lists in disjoint run registers -/
noncomputable section
set_option synthInstance.maxSize 16384
namespace OptimalQLS.Refinement.PhysicalProgram
open Matrix PolynomialTransform
variable {G H A B Q P : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype Q] [DecidableEq Q] [Fintype P] [DecidableEq P]

def liftInstruction (port : QueryPort Q P) (put : G → H) :
    NamedInstruction G A B Q → NamedInstruction H A B P
  | .gate g => .gate (put g)
  | .matrixCall p adj => .matrixCall (port.comp p) adj
  | .vectorCall p adj => .vectorCall (port.comp p) adj

def liftList (port : QueryPort Q P) (put : G → H) (c : NamedCircuit G A B Q) :
    NamedCircuit H A B P := c.map (liftInstruction port put)

theorem liftList_toQuery (port : QueryPort Q P) (put : G → H)
    (localEval : G → Matrix.unitaryGroup Q ℂ) (globalEval : H → Matrix.unitaryGroup P ℂ)
    (h : ∀ g, globalEval (put g)=port.apply (localEval g)) (c : NamedCircuit G A B Q) :
    (liftList port put c).toQuery globalEval=(c.toQuery localEval).lift port := by
  induction c with
  | nil => rfl
  | cons i c ih =>
    cases i <;> simp_all [liftList,liftInstruction,NamedCircuit.toQuery,NamedInstruction.toQuery,
      QueryCircuit.lift,QueryInstruction.lift]

theorem liftList_gates (port : QueryPort Q P) (put : G → H) (c : NamedCircuit G A B Q) :
    (liftList port put c).workGates=c.workGates := by
  induction c with
  | nil => rfl
  | cons i c ih => cases i <;> simp_all [liftList,liftInstruction,NamedCircuit.workGates]

end OptimalQLS.Refinement.PhysicalProgram
