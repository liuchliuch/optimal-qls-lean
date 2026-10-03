import OptimalQLS.Refinement.Repetition.Semantics

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.Refinement.Repetition
open Matrix LowerBounds
set_option maxHeartbeats 100000
universe u v
variable {A : Type u} {B : Type v} {d w : ℕ}
variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

attribute [local irreducible] repeatProgram

theorem repeatProgram_72000_success (c : QueryCircuit A B (Fin w)) (e : Fin d ↪ Fin w)
    (zero : Fin w) (out : Fin d) (UA : Matrix.unitaryGroup A ℂ)
    (Ub : Matrix.unitaryGroup B ℂ) (hp : 1 / 65536 < successMass c e zero UA Ub) :
    2 / 3 < (repeatProgram c e zero out 72000).successProbability UA Ub (basis zero) := by
  rw [repeatProgram_successProbability]
  have h := repetition_failure_bound hp (successMass_bounds c e zero out UA Ub).2
  calc
    (2 : ℝ) / 3 = 1 - 1 / 3 := by norm_num
    _ < 1 - (1 - successMass c e zero UA Ub) ^ 72000 := sub_lt_sub_left h 1



end OptimalQLS.Refinement.Repetition
