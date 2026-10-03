import OptimalQLS.Preparation.CompilerAttachment.Frames
import OptimalQLS.PolynomialTransform.ElementaryCircuit
import OptimalQLS.OracleSubstitution

/-! # Structural elementary-list attachment and oracle-role exchange -/
noncomputable section
set_option synthInstance.maxSize 4096
namespace OptimalQLS.Preparation.CompilerAttachment
open Matrix TransducerCompiler PolynomialTransform DirtyAncilla
variable {A B I D R P G : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype I] [DecidableEq I] [Fintype D] [DecidableEq D]
  [Fintype R] [DecidableEq R] [Fintype P] [DecidableEq P]

def attachInstruction (e : ElementarySpace I D × R ≃ P) (put : PhaseGate I → G) :
    ElementaryInstruction A B I D → NamedInstruction G A B P
  | .gate g => .gate (put g)
  | .matrixCall p b => .matrixCall ((scratchPort e).comp p) b
  | .vectorCall p b => .vectorCall ((scratchPort e).comp p) b

def attachList (e : ElementarySpace I D × R ≃ P) (put : PhaseGate I → G)
    (c : ElementaryCircuit A B I D) : NamedCircuit G A B P := c.map (attachInstruction e put)

theorem attachList_toQuery (e : ElementarySpace I D × R ≃ P) (put : PhaseGate I → G)
    (eval : G → Matrix.unitaryGroup P ℂ)
    (h : ∀ g, eval (put g)=GateSynthesis.placeHom e (elementaryPlacement g.eval))
    (c : ElementaryCircuit A B I D) :
    (attachList e put c).toQuery eval=c.toQuery.lift (scratchPort e) := by
  induction c with
  | nil => rfl
  | cons g c ih =>
    cases g <;> simp_all [attachList,attachInstruction,NamedCircuit.toQuery,
      NamedInstruction.toQuery,ElementaryCircuit.toQuery,ElementaryInstruction.toQuery,
      QueryCircuit.lift,QueryInstruction.lift,scratchPort_apply]

theorem attachList_workGates (e : ElementarySpace I D × R ≃ P) (put : PhaseGate I → G)
    (c : ElementaryCircuit A B I D) : (attachList e put c).workGates=c.workGates := by
  induction c with
  | nil => rfl
  | cons g c ih => cases g <;> simp_all [attachList,attachInstruction,NamedCircuit.workGates,
      ElementaryCircuit.workGates]

theorem attachList_eval (e : ElementarySpace I D × R ≃ P) (put : PhaseGate I → G)
    (eval : G → Matrix.unitaryGroup P ℂ)
    (h : ∀ g, eval (put g)=GateSynthesis.placeHom e (elementaryPlacement g.eval))
    (c : ElementaryCircuit A B I D) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    ((attachList e put c).toQuery eval).eval UA Ub=
      GateSynthesis.placeHom e (c.toQuery.eval UA Ub) := by
  rw [attachList_toQuery e put eval h,QueryCircuit.lift_eval,scratchPort_apply]

def swapElementaryInstruction : ElementaryInstruction A B I D → ElementaryInstruction B A I D
  | .gate g => .gate g
  | .matrixCall p b => .vectorCall p b
  | .vectorCall p b => .matrixCall p b

def swapElementary (c : ElementaryCircuit A B I D) : ElementaryCircuit B A I D :=
  c.map swapElementaryInstruction

theorem swapElementary_toQuery (c : ElementaryCircuit A B I D) :
    (swapElementary c).toQuery=c.toQuery.swapOracles := by
  induction c with
  | nil => rfl
  | cons g c ih => cases g <;> simp_all [swapElementary,swapElementaryInstruction,
      ElementaryCircuit.toQuery,ElementaryInstruction.toQuery,QueryCircuit.swapOracles,
      QueryInstruction.swapOracles]

theorem swapElementary_workGates (c : ElementaryCircuit A B I D) :
    (swapElementary c).workGates=c.workGates := by
  induction c with
  | nil => rfl
  | cons g c ih => cases g <;> simp_all [swapElementary,swapElementaryInstruction,
      ElementaryCircuit.workGates]

end OptimalQLS.Preparation.CompilerAttachment
