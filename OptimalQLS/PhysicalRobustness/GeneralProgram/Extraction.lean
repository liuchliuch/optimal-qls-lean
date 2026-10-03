import OptimalQLS.PhysicalRobustness.GeneralProgram.Target

/-! Extract only the algorithmic approximation; preserve the sharp noise constant. -/
noncomputable section
set_option maxHeartbeats 500000
open scoped Matrix.Norms.L2Operator
namespace OptimalQLS.PhysicalRobustness.GeneralProgram
open Matrix LowerBounds Reduction Refinement.Repetition
variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The exact right support retains over 15/16 of the actual accepting mass. -/
theorem noisy_direct_extraction (v : EuclideanSpace ℂ (D⊕D))
    (x : EuclideanSpace ℂ D) {ε : ℝ} (hx : ‖x‖=1)
    (hmass : 1/262144<‖v‖^2) (hε0 : 0<ε) (hε1 : ε<1/2)
    (herr : ‖NormedSpace.normalize v-WithLp.toLp 2 (rightState (WithLp.ofLp x))‖≤ε/2) :
    rightPart v≠0 ∧ ‖NormedSpace.normalize (rightPart v)‖=1 ∧
      ‖NormedSpace.normalize (rightPart v)-x‖≤ε ∧ 15/4194304<‖rightPart v‖^2 := by
  have hv : v≠0 := by intro hz; norm_num [hz] at hmass
  have he := extraction_guarantee (NormedSpace.normalize v) x
    (NormedSpace.norm_normalize hv) hx hε0 hε1 herr
  have hret : 15/16<‖rightPart (NormedSpace.normalize v)‖^2 := by
    have hsq : ε^2<1/4 := by nlinarith only [hε0,hε1]
    linarith only [hsq,he.2.2.1]
  have heq : ‖rightPart v‖^2=‖v‖^2*‖rightPart (NormedSpace.normalize v)‖^2 := by
    conv_lhs => rw [rightPart_scale_normalized v]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),mul_pow]
  have hprod := mul_lt_mul_of_pos_left hret (show 0<‖v‖^2 by linarith only [hmass])
  have hp : 15/4194304<‖rightPart v‖^2 := by rw [heq]; nlinarith only [hmass,hprod]
  have hr : rightPart v≠0 := by intro hz; norm_num [hz] at hp
  exact ⟨hr,NormedSpace.norm_normalize hr,
    by rw [normalize_rightPart v hv]; exact he.2.2.2.2.1,hp⟩

theorem direct_repetition_failure {p : ℝ} (hp : 15/4194304<p) (hp1 : p≤1) :
    (1-p)^600000<1/3 := by
  have hc : (3 : ℝ)<Real.exp (600000*(15/4194304)) := by
    have h := Real.add_one_le_exp ((600000 : ℝ)*(15/4194304))
    linarith
  have he : Real.exp ((600000 : ℕ)*(-p))≤Real.exp (-(600000*(15/4194304))) := by
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    linarith
  refine lt_of_le_of_lt ((failure_power_le_exp hp1 600000).trans he) ?_
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ)<3) hc

attribute [local irreducible] repeatProgram

theorem direct_repetition_success {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] {d w : ℕ}
    (c : QueryCircuit A B (Fin w)) (e : Fin d ↪ Fin w)
    (zero : Fin w) (out : Fin d) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (hp : 15/4194304<successMass c e zero UA Ub) :
    (2 : ℝ)/3<(repeatProgram c e zero out 600000).successProbability UA Ub (basis zero) ∧
    (repeatProgram c e zero out 600000).conditionalOutput UA Ub (basis zero)=
      pureDensity (normalizedSuccessVector c e zero UA Ub) := by
  have hp0 : 0<successMass c e zero UA Ub := lt_trans (by norm_num) hp
  constructor
  · rw [repeatProgram_successProbability]
    have hf := direct_repetition_failure hp (successMass_bounds c e zero out UA Ub).2
    calc
      (2 : ℝ)/3=1-1/3 := by norm_num
      _ < 1-(1-successMass c e zero UA Ub)^600000 := sub_lt_sub_left hf 1
  · exact repeatProgram_conditionalOutput_pure c e zero out 600000 UA Ub hp0 (by decide)

/-- Right-coordinate restriction is contractive without renormalization. -/
theorem rightPart_dist_le (v w : EuclideanSpace ℂ (D⊕D)) :
    ‖rightPart v-rightPart w‖≤‖v-w‖ := by
  have hp := parts_norm_sq (v-w)
  have he : rightPart (v-w)=rightPart v-rightPart w := rfl
  rw [he] at hp
  nlinarith [sq_nonneg ‖leftPart (v-w)‖,norm_nonneg (v-w),norm_nonneg (rightPart v-rightPart w)]

end OptimalQLS.PhysicalRobustness.GeneralProgram
