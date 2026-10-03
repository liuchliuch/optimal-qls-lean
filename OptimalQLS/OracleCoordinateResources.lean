import OptimalQLS.OracleCoordinates

/-! Structural resources and exact terminal paths under oracle-register coordinates. -/
noncomputable section
namespace OptimalQLS.OracleCoordinates
open Matrix LowerBounds Refinement.Repetition
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
universe u v u' v'
variable {A : Type u} {B : Type v} {A' : Type u'} {B' : Type v'}
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B']

/-- Only query-port coordinates change; all non-query nodes remain identical. -/
theorem program_instrumentDepth (ea : A ≃ A') (eb : B ≃ B') {d w : ℕ}
    (c : FiniteOracleProgram A B d w) :
    instrumentDepth (program ea eb c)=instrumentDepth c := by
  induction c with
  | output s a => rfl
  | matrixQuery p a c ih => exact ih
  | vectorQuery p a c ih => exact ih
  | instrument r dims K hn cs ih => simp only [program,instrumentDepth,ih]

/-- Every old terminal has exactly the same measurement outcomes after relabeling. -/
def terminalEquiv (ea : A ≃ A') (eb : B ≃ B') {d : ℕ} :
    {w : ℕ} → (c : FiniteOracleProgram A B d w) → c.Terminal ≃ (program ea eb c).Terminal
  | _,.output _ _ => Equiv.refl _
  | _,.matrixQuery _ _ c => terminalEquiv ea eb c
  | _,.vectorQuery _ _ c => terminalEquiv ea eb c
  | _,.instrument _ _ _ _ cs => Equiv.sigmaCongrRight (fun i=>terminalEquiv ea eb (cs i))

def path (ea : A ≃ A') (eb : B ≃ B') :
    {w : ℕ} → VariableQueryPath A B w → VariableQueryPath A' B' w
  | _,.initial v => .initial v
  | _,.work K c => .work K (path ea eb c)
  | _,.matrixQuery p adj c => .matrixQuery (port ea p) adj (path ea eb c)
  | _,.vectorQuery p adj c => .vectorQuery (port eb p) adj (path ea eb c)

theorem path_queries (ea : A ≃ A') (eb : B ≃ B') {w : ℕ} (c : VariableQueryPath A B w) :
    (path ea eb c).matrixQueries=c.matrixQueries ∧ (path ea eb c).vectorQueries=c.vectorQueries := by
  induction c with
  | initial v => exact ⟨rfl,rfl⟩
  | work K c ih => exact ih
  | matrixQuery p adj c ih => exact ⟨congrArg (fun n=>n+1) ih.1,ih.2⟩
  | vectorQuery p adj c ih => exact ⟨ih.1,congrArg (fun n=>n+1) ih.2⟩

/-- Exact path transport, with the same initial vector and rectangular Kraus leaves. -/
theorem program_terminalPath (ea : A ≃ A') (eb : B ≃ B') {d w : ℕ}
    (c : FiniteOracleProgram A B d w) (v : VariableQueryPath A B w) (k : c.Terminal) :
    (program ea eb c).terminalPath (path ea eb v) (terminalEquiv ea eb c k)=
      path ea eb (c.terminalPath v k) := by
  induction c with
  | output s a => rfl
  | matrixQuery p adj c ih => exact ih (.matrixQuery p adj v) k
  | vectorQuery p adj c ih => exact ih (.vectorQuery p adj v) k
  | instrument r dims K hn cs ih => exact ih k.1 (.work (K k.1) v) k.2

/-- Pathwise equality includes rejected and zero-weight paths. -/
theorem program_terminal_queries (ea : A ≃ A') (eb : B ≃ B') {d w : ℕ}
    (c : FiniteOracleProgram A B d w) (v : VariableQueryPath A B w) (k : c.Terminal) :
    ((program ea eb c).terminalPath (path ea eb v) (terminalEquiv ea eb c k)).matrixQueries=
      (c.terminalPath v k).matrixQueries ∧
    ((program ea eb c).terminalPath (path ea eb v) (terminalEquiv ea eb c k)).vectorQueries=
      (c.terminalPath v k).vectorQueries := by
  rw [program_terminalPath]
  exact path_queries ea eb _

end OptimalQLS.OracleCoordinates
