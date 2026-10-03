import OptimalQLS.OracleComposition

noncomputable section
namespace OptimalQLS
variable {A B S W : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype S] [DecidableEq S] [Fintype W] [DecidableEq W]

def QueryInstruction.swapOracles : QueryInstruction A B W → QueryInstruction B A W
  | .work U => .work U
  | .matrixCall p b => .vectorCall p b
  | .vectorCall p b => .matrixCall p b

def QueryCircuit.swapOracles (c : QueryCircuit A B W) : QueryCircuit B A W :=
  c.map QueryInstruction.swapOracles

theorem QueryCircuit.swapOracles_eval (c : QueryCircuit A B W)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    c.swapOracles.eval Ub UA=c.eval UA Ub := by
  induction c with
  | nil => rfl
  | cons g c ih =>
    cases g <;> simp_all [swapOracles,QueryInstruction.swapOracles,eval,QueryInstruction.eval]

theorem QueryCircuit.swapOracles_counts (c : QueryCircuit A B W) :
    c.swapOracles.matrixQueries=c.vectorQueries ∧ c.swapOracles.vectorQueries=c.matrixQueries := by
  induction c with
  | nil => simp [swapOracles,matrixQueries,vectorQueries]
  | cons g c ih =>
    cases g <;> simp_all [swapOracles,QueryInstruction.swapOracles,matrixQueries,vectorQueries]

/-- Substitute the actual whole-vector-oracle realization, with controls and
adjoints inherited from its literal instruction list. -/
def QueryCircuit.substituteVector (c : QueryCircuit A B W) (d : QueryCircuit A S B) :
    QueryCircuit A S W := (c.swapOracles.substituteMatrix d.swapOracles).swapOracles

theorem QueryCircuit.substituteVector_eval (c : QueryCircuit A B W) (d : QueryCircuit A S B)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup S ℂ) :
    (c.substituteVector d).eval UA Ub=c.eval UA (d.eval UA Ub) := by
  rw [substituteVector,swapOracles_eval,substituteMatrix_eval,swapOracles_eval,swapOracles_eval]

theorem QueryCircuit.substituteVector_counts (c : QueryCircuit A B W) (d : QueryCircuit A S B) :
    (c.substituteVector d).matrixQueries=c.matrixQueries+c.vectorQueries*d.matrixQueries ∧
    (c.substituteVector d).vectorQueries=c.vectorQueries*d.vectorQueries := by
  have hs := swapOracles_counts (c.swapOracles.substituteMatrix d.swapOracles)
  have hc := substituteMatrix_counts d.swapOracles c.swapOracles
  rw [(swapOracles_counts c).1,(swapOracles_counts c).2,
    (swapOracles_counts d).1,(swapOracles_counts d).2] at hc
  change _ ∧ _
  exact ⟨hs.1.trans (hc.2.trans (Nat.add_comm _ _)),hs.2.trans hc.1⟩

end OptimalQLS
