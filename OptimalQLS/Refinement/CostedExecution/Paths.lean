import OptimalQLS.Refinement.CostedExecution.Syntax

/-! Costs on every syntactic terminal branch, including zero-weight branches. -/
noncomputable section
namespace OptimalQLS.Refinement.CostedExecution.Program
variable {G A B Aux Data : Type*} {d w : ℕ}

def Terminal : Program G A B Aux Data w → Type
  | .named _ next => next.Terminal
  | .matrixCall _ _ next => next.Terminal
  | .vectorCall _ _ next => next.Terminal
  | .measure _ next => (b : Bool) × (next b).Terminal
  | .bitX _ next => next.Terminal
  | .discard _ => Unit

def terminalCost : (p : Program G A B Aux Data w) → p.Terminal → ℕ
  | .named _ next, k => next.terminalCost k + 1
  | .matrixCall _ _ next, k => next.terminalCost k
  | .vectorCall _ _ next, k => next.terminalCost k
  | .measure _ next, k => (next k.1).terminalCost k.2 + 1
  | .bitX _ next, k => next.terminalCost k + 1
  | .discard _, _ => 0

theorem terminalCost_le (p : Program G A B Aux Data w) (k : p.Terminal) :
    p.terminalCost k ≤ p.cost := by
  induction p with
  | named g next ih => exact Nat.add_le_add_right (ih k) 1
  | matrixCall p b next ih => exact ih k
  | vectorCall p b next ih => exact ih k
  | measure i next ih =>
    rcases k with ⟨b,k⟩
    cases b with
    | false => exact Nat.add_le_add_right ((ih false k).trans (Nat.le_max_left _ _)) 1
    | true => exact Nat.add_le_add_right ((ih true k).trans (Nat.le_max_right _ _)) 1
  | bitX i next ih => exact Nat.add_le_add_right (ih k) 1
  | discard flag => exact le_rfl

variable [Fintype Aux] [DecidableEq Aux] [Fintype Data] [DecidableEq Data]
open Matrix LowerBounds

/-- Every terminal branch of the lowered normalized-instrument program projects
to its actual primitive branch. Discard outcomes consume no further operations. -/
def projectTerminal (E : State Aux Data ≃ Fin w) (F : (Data → Bool) ≃ Fin d)
    (gate : G → Matrix.unitaryGroup (Fin w) ℂ) :
    (p : Program G A B Aux Data w) → (p.lower E F gate).Terminal → p.Terminal
  | .named _ next, k => projectTerminal E F gate next k.2
  | .matrixCall _ _ next, k => projectTerminal E F gate next k
  | .vectorCall _ _ next, k => projectTerminal E F gate next k
  | .measure _ next, k => ⟨outcome k.1,projectTerminal E F gate (next (outcome k.1)) k.2⟩
  | .bitX _ next, k => projectTerminal E F gate next k.2
  | .discard _, _ => ()

theorem lowered_terminalCost_le (E : State Aux Data ≃ Fin w) (F : (Data → Bool) ≃ Fin d)
    (gate : G → Matrix.unitaryGroup (Fin w) ℂ) (p : Program G A B Aux Data w)
    (k : (p.lower E F gate).Terminal) :
    p.terminalCost (p.projectTerminal E F gate k)≤p.cost := p.terminalCost_le _

end OptimalQLS.Refinement.CostedExecution.Program
