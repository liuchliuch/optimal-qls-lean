import OptimalQLS.LowerBounds.HaltingInstrument
import OptimalQLS.LowerBounds.VectorPerturbationScalars

/-!
# A literal success-and-direction measurement separates solver outputs

The successful block is the success probability times the conditional output.
Failure occupies its own arbitrary finite register. Only actual trace distance
and a bounded matrix observable occur in the hypotheses and conclusion.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
variable {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

def successObservable (T : Matrix D D ℂ) : Matrix (D ⊕ E) (D ⊕ E) ℂ :=
  Matrix.fromBlocks T 0 0 0

def flaggedOutput (p : ℝ) (rho : Matrix D D ℂ) (failure : Matrix E E ℂ) :
    Matrix (D ⊕ E) (D ⊕ E) ℂ := Matrix.fromBlocks (p • rho) 0 0 failure

theorem successObservable_norm_le_one (T : Matrix D D ℂ) (hT : ‖T‖ ≤ 1) :
    ‖successObservable (E := E) T‖ ≤ 1 := by
  rw [successObservable, blockDiagonal_norm]
  exact max_le hT (by simp)

theorem successObservable_expectation (T rho : Matrix D D ℂ) (p : ℝ) (failure : Matrix E E ℂ) :
    (successObservable T * flaggedOutput p rho failure).trace.re = p * (T * rho).trace.re := by
  rw [successObservable, flaggedOutput, Matrix.fromBlocks_multiply]
  simp [trace_blockDiagonal, Matrix.mul_smul]

/-- Conditional accuracy within 1/64 and successful fixed-direction weight
at least25/61 force an unconditional flagged trace distance at least1/10. -/
theorem flagged_solver_outputs_separated (T target target' rho rho' : Matrix D D ℂ)
    (failure failure' : Matrix E E ℂ) (p p' eps : ℝ)
    (hT : ‖T‖ ≤ 1) (htarget : (T * target).trace.re = 0)
    (htarget' : (25 / 61 : ℝ) ≤ (T * target').trace.re)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hp' : 2 / 3 ≤ p') (hp1' : p' ≤ 1)
    (herr : traceDistance rho target ≤ eps) (herr' : traceDistance rho' target' ≤ eps)
    (heps : eps ≤ 1 / 64) :
    (1 / 10 : ℝ) ≤ traceDistance (flaggedOutput p rho failure) (flaggedOutput p' rho' failure') := by
  have heps0 : 0 ≤ eps := (traceDistance_nonneg rho target).trans herr
  have hold := bounded_observable_difference T rho target hT
  rw [htarget, sub_zero] at hold
  have hold' : (T * rho).trace.re ≤ 2 * eps :=
    (le_abs_self _).trans (hold.trans (by linarith))
  have holdEvent : p * (T * rho).trace.re ≤ 2 * eps :=
    (mul_le_mul_of_nonneg_left hold' hp).trans (by nlinarith)
  have hnew := bounded_observable_difference T rho' target' hT
  have hnew' : 25 / 61 - 2 * eps ≤ (T * rho').trace.re := by
    have := neg_abs_le ((T * rho').trace.re - (T * target').trace.re)
    linarith
  have hp0' : 0 ≤ p' := by linarith
  have hnewEvent := mul_le_mul_of_nonneg_left hnew' hp0'
  have hgap := success_direction_event_gap (eps := 2 * eps) (p := p') (by linarith)
    hp' hp1' holdEvent hnewEvent
  have hobs := bounded_observable_difference (successObservable (E := E) T)
    (flaggedOutput p' rho' failure') (flaggedOutput p rho failure) (successObservable_norm_le_one T hT)
  rw [successObservable_expectation, successObservable_expectation] at hobs
  rw [traceDistance_symm] at hobs
  have hle := le_abs_self (p' * (T * rho').trace.re - p * (T * rho).trace.re)
  linarith

end OptimalQLS.LowerBounds
