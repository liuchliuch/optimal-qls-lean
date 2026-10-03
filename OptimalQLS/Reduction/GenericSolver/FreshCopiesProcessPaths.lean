import OptimalQLS.Reduction.GenericSolver.FreshCopiesProcessResources

/-! Elementary unitary and one-bit measurement costs on every terminal of the
actual lowered program. Trace outcomes remain in these terminals and contribute
no unitary gates. No probability or oracle assumption restricts the bounds. -/
noncomputable section
namespace OptimalQLS.Reduction.GenericSolver.FreshCopies.Process
open Matrix LowerBounds Refinement.CostedExecution
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
variable {A B VA VB : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  {argumentsA : A ≃ (VA → Bool)} {argumentsB : B ≃ (VB → Bool)} {O R : Register}

/-- Each charged node is the actual local unitary supplied to `lower`; the
singleton outcome is removed only when descending to its actual continuation. -/
def terminalWork : {R : Register} → (p : Process argumentsA argumentsB O R) →
    p.lower.Terminal → ℕ
  | _, .unitary _ _ next, k => next.terminalWork k.2 + 1
  | _, .matrix _ _ _ next, k => next.terminalWork k
  | _, .vector _ _ _ next, k => next.terminalWork k
  | _, .measure _ next, k => (next (outcome k.1)).terminalWork k.2
  | _, .trace _ next, k => next.terminalWork k.2
  | _, .output _, _ => 0

def terminalMeasurements : {R : Register} → (p : Process argumentsA argumentsB O R) →
    p.lower.Terminal → ℕ
  | _, .unitary _ _ next, k => next.terminalMeasurements k.2
  | _, .matrix _ _ _ next, k => next.terminalMeasurements k
  | _, .vector _ _ _ next, k => next.terminalMeasurements k
  | _, .measure _ next, k => (next (outcome k.1)).terminalMeasurements k.2 + 1
  | _, .trace _ next, k => next.terminalMeasurements k.2
  | _, .output _, _ => 0

theorem terminalWork_le (p : Process argumentsA argumentsB O R) (k : p.lower.Terminal) :
    p.terminalWork k ≤ p.work := by
  induction p with
  | unitary U h next ih => exact Nat.add_le_add_right (ih k.2) 1
  | matrix port adj L next ih => exact ih k
  | vector port adj L next ih => exact ih k
  | measure i next ih =>
    change (next (outcome k.1)).terminalWork k.2 ≤ max (next false).work (next true).work
    have h : ∀ b, (next b).work ≤ max (next false).work (next true).work := by
      intro b
      cases b
      · exact Nat.le_max_left _ _
      · exact Nat.le_max_right _ _
    exact (ih (outcome k.1) k.2).trans (h _)
  | trace F next ih => exact ih k.2
  | output flag => exact le_rfl

theorem terminalMeasurements_le (p : Process argumentsA argumentsB O R)
    (k : p.lower.Terminal) : p.terminalMeasurements k ≤ p.measurements := by
  induction p with
  | unitary U h next ih => exact ih k.2
  | matrix port adj L next ih => exact ih k
  | vector port adj L next ih => exact ih k
  | measure i next ih =>
    change (next (outcome k.1)).terminalMeasurements k.2 + 1 ≤
      max (next false).measurements (next true).measurements + 1
    apply Nat.add_le_add_right
    have h : ∀ b, (next b).measurements ≤ max (next false).measurements (next true).measurements := by
      intro b
      cases b
      · exact Nat.le_max_left _ _
      · exact Nat.le_max_right _ _
    exact (ih (outcome k.1) k.2).trans (h _)
  | trace F next ih => exact ih k.2
  | output flag => exact le_rfl

theorem terminalPath_matrixQueries_le (p : Process argumentsA argumentsB O R)
    (path : VariableQueryPath A B R.dimension) (k : p.lower.Terminal) :
    (p.lower.terminalPath path k).matrixQueries ≤ path.matrixQueries + p.matrixCalls := by
  simpa only [p.lower_matrixCalls] using
    Refinement.Repetition.terminalPath_matrixQueries_le p.lower path k

theorem terminalPath_vectorQueries_le (p : Process argumentsA argumentsB O R)
    (path : VariableQueryPath A B R.dimension) (k : p.lower.Terminal) :
    (p.lower.terminalPath path k).vectorQueries ≤ path.vectorQueries + p.vectorCalls := by
  simpa only [p.lower_vectorCalls] using
    Refinement.Repetition.terminalPath_vectorQueries_le p.lower path k

/-- Same-tree resources for every terminal, including zero-amplitude outcomes
and either success flag, from an arbitrary input state. -/
theorem terminal_resources (p : Process argumentsA argumentsB O R)
    (psi : Fin R.dimension → ℂ) (k : p.lower.Terminal) :
    (p.lower.terminalPath (.initial psi) k).matrixQueries ≤ p.matrixCalls ∧
    (p.lower.terminalPath (.initial psi) k).vectorQueries ≤ p.vectorCalls ∧
    p.terminalWork k ≤ p.work ∧ p.terminalMeasurements k ≤ p.measurements := by
  refine ⟨?_, ?_, p.terminalWork_le k, p.terminalMeasurements_le k⟩
  · simpa only [VariableQueryPath.matrixQueries, Nat.zero_add] using
      p.terminalPath_matrixQueries_le (.initial psi) k
  · simpa only [VariableQueryPath.vectorQueries, Nat.zero_add] using
      p.terminalPath_vectorQueries_le (.initial psi) k

end OptimalQLS.Reduction.GenericSolver.FreshCopies.Process
