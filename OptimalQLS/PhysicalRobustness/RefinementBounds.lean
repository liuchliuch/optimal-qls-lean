import OptimalQLS.RefinementAnalytic

/-! Numerical postselection bounds for the concrete noisy correction. -/
noncomputable section
namespace OptimalQLS.PhysicalRobustness
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℝ E] [NormedSpace ℝ F]

theorem noisy_correction_filter_error (C D : E →L[ℝ] F) (y y₀ : E) (x : F)
    {η lam : ℝ} (hη : 0≤η) (hC : ‖C‖≤3/4) (hCD : ‖C-D‖≤5*η/4)
    (hy : ‖y-y₀‖≤η) (hy₀ : ‖y₀‖≤1) (hcorrect : D y₀=lam • x) :
    ‖C y-lam • x‖≤2*η := by
  have hid : C y-lam • x=C (y-y₀)+(C-D) y₀ := by
    simp only [map_sub,ContinuousLinearMap.sub_apply,hcorrect]
    abel
  rw [hid]
  calc
    _ ≤ ‖C (y-y₀)‖+‖(C-D) y₀‖ := norm_add_le _ _
    _ ≤ (3/4)*η+(5*η/4)*1 := add_le_add
      ((C.le_opNorm _).trans (mul_le_mul hC hy (norm_nonneg _) (by norm_num)))
      (((C-D).le_opNorm _).trans (mul_le_mul hCD hy₀ (norm_nonneg _) (by positivity)))
    _ = 2*η := by ring

theorem noisy_refinement_state_and_probability (x z : E) (hx : ‖x‖=1)
    {ε lam : ℝ} (hε0 : 0<ε) (hε1 : ε<1/2) (hlam : 1/384≤lam)
    (hz : ‖z-lam • x‖≤2*(ε/4096)) :
    z≠0 ∧ ‖NormedSpace.normalize z-x‖≤ε/2 ∧ 1/262144<‖z‖^2 := by
  have hp : 0<lam := by linarith
  have hn : ‖lam • x‖=lam := by simp [norm_smul,hx,abs_of_pos hp]
  have hr := norm_sub_norm_le (lam • x) z
  rw [hn,norm_sub_rev] at hr
  have hzn : 1/512<‖z‖ := by linarith
  have hzne : z≠0 := norm_pos_iff.mp (by linarith : 0<‖z‖)
  have hxne : lam • x≠0 := norm_ne_zero_iff.mp (by rw [hn]; exact hp.ne')
  have he := Perturbation.normalize_sub_le z (lam • x) hzne hxne
  rw [NormedSpace.normalize_smul_of_pos hp,
    NormedSpace.normalize_eq_self_of_norm_eq_one hx,hn] at he
  refine ⟨hzne,he.trans ?_,?_⟩
  · apply (div_le_iff₀ hp).mpr
    have hm := mul_le_mul_of_nonneg_left hlam hε0.le
    nlinarith
  · nlinarith

end OptimalQLS.PhysicalRobustness
