import OptimalQLS.Refinement.Repetition.Complete

/-! # Constant repetition for the noisy-input accepting mass -/
noncomputable section
namespace OptimalQLS.Refinement.Repetition
open Matrix LowerBounds
set_option maxHeartbeats 100000
attribute [local irreducible] repeatProgram

theorem noisy_repetition_failure {p : ℝ} (hp : 1/262144<p) (hp1 : p≤1) :
    (1-p)^600000<1/3 := by
  have hc : (3 : ℝ)<Real.exp (600000/262144) := by
    have h := Real.add_one_le_exp ((600000 : ℝ)/262144)
    linarith
  have he : Real.exp ((600000 : ℕ)*(-p))≤Real.exp (-(600000/262144)) := by
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    linarith
  refine lt_of_le_of_lt ((failure_power_le_exp hp1 600000).trans he) ?_
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ)<3) hc

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] {d w : ℕ}

theorem repeatProgram_600000_success (c : QueryCircuit A B (Fin w)) (e : Fin d ↪ Fin w)
    (zero : Fin w) (out : Fin d) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (hp : 1/262144<successMass c e zero UA Ub) :
    (2 : ℝ)/3<(repeatProgram c e zero out 600000).successProbability UA Ub (basis zero) := by
  rw [repeatProgram_successProbability]
  have hf := noisy_repetition_failure hp (successMass_bounds c e zero out UA Ub).2
  calc
    (2 : ℝ)/3=1-1/3 := by norm_num
    _ < 1-(1-successMass c e zero UA Ub)^600000 := sub_lt_sub_left hf 1

/-- Every claim concerns the same literal finite measurement/reset program. -/
theorem operational_repetition_600000 (c : QueryCircuit A B (Fin w)) (e : Fin d ↪ Fin w)
    (zero : Fin w) (out : Fin d) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (hp : 1/262144<successMass c e zero UA Ub) :
    (2 : ℝ)/3<(repeatProgram c e zero out 600000).successProbability UA Ub (basis zero) ∧
    (repeatProgram c e zero out 600000).conditionalOutput UA Ub (basis zero)=
      pureDensity (normalizedSuccessVector c e zero UA Ub) ∧
    ‖WithLp.toLp 2 (normalizedSuccessVector c e zero UA Ub)‖=1 ∧
    matrixDepth (repeatProgram c e zero out 600000)≤600000*c.matrixQueries ∧
    (repeatProgram c e zero out 600000).vectorDepth≤600000*c.vectorQueries ∧
    RegisterBound w (repeatProgram c e zero out 600000) ∧
    instrumentDepth (repeatProgram c e zero out 600000)≤600000*(workCount c+1)+1 := by
  have hp0 : 0<successMass c e zero UA Ub := lt_trans (by norm_num) hp
  exact ⟨repeatProgram_600000_success c e zero out UA Ub hp,
    repeatProgram_conditionalOutput_pure c e zero out 600000 UA Ub hp0 (by decide),
    normalizedSuccessVector_norm c e zero UA Ub hp0,
    repeatProgram_matrixDepth c e zero out 600000,
    repeatProgram_vectorDepth c e zero out 600000,
    repeatProgram_registerBound c e zero out 600000,
    repeatProgram_instrumentDepth c e zero out 600000⟩

end OptimalQLS.Refinement.Repetition
