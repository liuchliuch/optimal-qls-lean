import OptimalQLS.Reduction.Complete
import OptimalQLS.Refinement.Repetition.NoisySuccess

/-! Directly postselecting the dilation head in each physical attempt. -/
noncomputable section
open scoped Matrix.Norms.L2Operator
namespace OptimalQLS.Reduction
open Matrix LowerBounds Refinement.Repetition
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
variable {D : Type*} [Fintype D] [DecidableEq D]

theorem rightPart_smul (r : ℝ) (v : EuclideanSpace ℂ (D⊕D)) :
    rightPart (r • v)=r • rightPart v := rfl

theorem rightPart_scale_normalized (v : EuclideanSpace ℂ (D⊕D)) :
    rightPart v=‖v‖ • rightPart (NormedSpace.normalize v) := by
  rw [←rightPart_smul,NormedSpace.norm_smul_normalize]

theorem normalize_rightPart (v : EuclideanSpace ℂ (D⊕D)) (hv : v≠0) :
    NormedSpace.normalize (rightPart v)=
      NormedSpace.normalize (rightPart (NormedSpace.normalize v)) := by
  rw [rightPart_scale_normalized v,NormedSpace.normalize_smul_of_pos (norm_pos_iff.mpr hv)]

/-- The full accepted amplitude is retained, so the lower bound is the actual
Born mass of the joint auxiliary-and-head measurement. -/
theorem direct_extraction_guarantee (v : EuclideanSpace ℂ (D⊕D))
    (x : EuclideanSpace ℂ D) {ε : ℝ} (hx : ‖x‖=1)
    (hmass : 1/65536<‖v‖^2) (hε0 : 0<ε) (hε1 : ε<1/2)
    (herr : ‖NormedSpace.normalize v-WithLp.toLp 2 (rightState (WithLp.ofLp x))‖≤ε/2) :
    rightPart v≠0 ∧ ‖NormedSpace.normalize (rightPart v)‖=1 ∧
      ‖NormedSpace.normalize (rightPart v)-x‖≤ε ∧ 1/262144<‖rightPart v‖^2 := by
  have hv : v≠0 := by intro hz; norm_num [hz] at hmass
  have he := extraction_guarantee (NormedSpace.normalize v) x
    (NormedSpace.norm_normalize hv) hx hε0 hε1 herr
  have heq : ‖rightPart v‖^2=‖v‖^2*‖rightPart (NormedSpace.normalize v)‖^2 := by
    conv_lhs => rw [rightPart_scale_normalized v]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),mul_pow]
  have hprod := mul_le_mul_of_nonneg_left he.2.2.2.1 (sq_nonneg ‖v‖)
  have hp : 1/262144<‖rightPart v‖^2 := by
    rw [heq]
    nlinarith only [hmass,hprod]
  have hr : rightPart v≠0 := by intro hz; norm_num [hz] at hp
  exact ⟨hr,NormedSpace.norm_normalize hr,
    by rw [normalize_rightPart v hv]; exact he.2.2.2.2.1,hp⟩

end OptimalQLS.Reduction
