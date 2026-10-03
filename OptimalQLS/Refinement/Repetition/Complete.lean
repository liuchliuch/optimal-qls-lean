import OptimalQLS.Refinement.Repetition.Success
import OptimalQLS.Refinement.Repetition.Resources
import OptimalQLS.Refinement.Repetition.PhysicalRefinement
import OptimalQLS.Refinement.Repetition.Transport

/-! The operational repetition theorem for one literal two-oracle circuit. -/
noncomputable section
open scoped Matrix.Norms.L2Operator
namespace OptimalQLS.Refinement.Repetition
open Matrix LowerBounds
universe u v
variable {A : Type u} {B : Type v} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] {d w : ℕ}
attribute [local irreducible] repeatProgram

/-- All claims refer to the same explicitly constructed finite quantum
program. The sole quantitative premise is its actual one-run accepted mass.
There is no independent-runs, output-channel, or uniform-output certificate. -/
theorem operational_repetition_72000 (c : QueryCircuit A B (Fin w))
    (e : Fin d ↪ Fin w) (zero : Fin w) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (hp : 1 / 65536 < successMass c e zero UA Ub) :
    (2 : ℝ) / 3 < (repeatProgram c e zero out 72000).successProbability UA Ub (basis zero) ∧
    ((repeatProgram c e zero out 72000).executeDensity UA Ub Bool.not (basis zero)).trace.re < 1 / 3 ∧
    (repeatProgram c e zero out 72000).conditionalOutput UA Ub (basis zero) =
      pureDensity (normalizedSuccessVector c e zero UA Ub) ∧
    ‖WithLp.toLp 2 (normalizedSuccessVector c e zero UA Ub)‖ = 1 ∧
    matrixDepth (repeatProgram c e zero out 72000) ≤ 72000 * c.matrixQueries ∧
    (repeatProgram c e zero out 72000).vectorDepth ≤ 72000 * c.vectorQueries ∧
    RegisterBound w (repeatProgram c e zero out 72000) ∧
    instrumentDepth (repeatProgram c e zero out 72000) ≤ 72000 * (workCount c + 1) + 1 := by
  have hp0 : 0 < successMass c e zero UA Ub := lt_trans (by norm_num) hp
  refine ⟨repeatProgram_72000_success c e zero out UA Ub hp, ?_,
    repeatProgram_conditionalOutput_pure c e zero out 72000 UA Ub hp0 (by decide),
    normalizedSuccessVector_norm c e zero UA Ub hp0,
    repeatProgram_matrixDepth c e zero out 72000,
    repeatProgram_vectorDepth c e zero out 72000,
    repeatProgram_registerBound c e zero out 72000,
    repeatProgram_instrumentDepth c e zero out 72000⟩
  rw [repeatProgram_failureProbability]
  exact repetition_failure_bound hp (successMass_bounds c e zero out UA Ub).2

end OptimalQLS.Refinement.Repetition
