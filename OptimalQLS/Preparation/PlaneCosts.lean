import OptimalQLS.Lemma47
import OptimalQLS.Preparation.Costs

noncomputable section
namespace OptimalQLS.Preparation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The norm squares are the exact orthogonal weights of the two real-plane components. -/
theorem plane_pseudoinverse_energy (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (e : E) (he : ‖e‖=1) (Z : E →L[ℂ] E) (hZP : Z (K.starProjection e)=0)
    {s : ℝ} (hs : 0≤s) (hZe : ‖Z e‖≤s) (hhalf : ‖K.starProjection e‖^2≤1/2)
    (q : E) (hq : q ∈ Submodule.span ℝ ({K.starProjection e,e-K.starProjection e} : Set E)) :
    ‖q‖^2 = ‖K.starProjection q‖^2+‖q-K.starProjection q‖^2 ∧
    ‖Z q‖^2 ≤ 2*s^2*‖q-K.starProjection q‖^2 := by
  have horth : inner ℂ (K.starProjection q) (q-K.starProjection q)=0 := by
    exact inner_eq_zero_symm.mp (K.starProjection_inner_eq_zero q _ (K.starProjection_apply_mem q))
  have hnorm : ‖q‖^2 = ‖K.starProjection q‖^2+‖q-K.starProjection q‖^2 := by
    have h := norm_add_sq (𝕜 := ℂ) (K.starProjection q) (q-K.starProjection q)
    have hh : K.starProjection q+(q-K.starProjection q)=q := by abel
    rw [hh,horth,RCLike.zero_re] at h
    simpa using h
  refine ⟨hnorm,?_⟩
  obtain ⟨a,b,hq⟩ := Submodule.mem_span_pair.mp hq
  have hlin (T : E →L[ℂ] E) (c : ℝ) (v : E) : T (c • v)=c • T v :=
    T.toLinearMap.map_smul_of_tower c v
  have hPp : K.starProjection (K.starProjection e)=K.starProjection e :=
    Submodule.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem e)
  have hpq : K.starProjection q=a • K.starProjection e := by
    rw [← hq,map_add,hlin,hlin,map_sub,hPp,sub_self,smul_zero,add_zero]
  have hqminus : q-K.starProjection q=b • (e-K.starProjection e) := by rw [hpq,← hq]; abel
  have hzq : Z q=b • Z e := by
    rw [← hq,map_add,hlin,hlin,map_sub,hZP,smul_zero,zero_add,sub_zero]
  have hweight : 1/2 ≤ ‖e-K.starProjection e‖^2 := by
    have h := (kernelProjection_plane_data K e he).2.1
    linarith
  have hZe2 : ‖Z e‖^2 ≤ s^2 := sq_le_sq₀ (norm_nonneg _) hs |>.mpr hZe
  rw [hzq,hqminus,norm_smul,norm_smul,Real.norm_eq_abs,mul_pow,mul_pow,sq_abs]
  have hscale := mul_le_mul_of_nonneg_left hZe2 (sq_nonneg b)
  have hweight' := mul_le_mul_of_nonneg_left hweight (show 0≤2*s^2*b^2 by positivity)
  nlinarith

/-- Actual Hilbert-space costs, with no supplied decomposition weights. -/
theorem preparation_plane_costs (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (e : E) (he : ‖e‖=1) (Z : E →L[ℂ] E) (hZP : Z (K.starProjection e)=0)
    {κ s ŝ α : ℝ} (hκ : 0<κ) (hs : 1≤s) (hshlo : 3*s/8≤ŝ) (hshhi : ŝ≤5*s/2)
    (hα : 0<α) (hα2 : α≤2) (hZe : ‖Z e‖≤s) (hhalf : ‖K.starProjection e‖^2≤1/2)
    (q : E) (hq : q ∈ Submodule.span ℝ ({K.starProjection e,e-K.starProjection e} : Set E))
    (hQ : ‖q‖^2≤κ/(3*s)) :
    2*α*(ŝ*‖K.starProjection q‖^2+‖Z q‖^2/ŝ)<8*κ ∧
    2*α*(ŝ*‖K.starProjection q‖^2+‖Z q‖^2/ŝ)+2*‖q‖^2<9*κ := by
  obtain ⟨hN,hZ⟩ := plane_pseudoinverse_energy K e he Z hZP (by linarith : 0≤s) hZe hhalf q hq
  have h := preparation_cost_bounds hκ hs hshlo hshhi hα hα2
    (sq_nonneg ‖K.starProjection q‖) (sq_nonneg ‖q-K.starProjection q‖) (sq_nonneg ‖Z q‖) hZ
    (by rwa [← hN])
  rwa [← hN] at h

end OptimalQLS.Preparation
