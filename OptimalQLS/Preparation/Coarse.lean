import OptimalQLS.Preparation.Output

noncomputable section
namespace OptimalQLS.Preparation
open Matrix TransducerCompiler Alignment
set_option synthInstance.maxSize 2048
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Exact real alignment and the actual finite-vector error yield a positive
constant amplitude; no postselection approximation is substituted here. -/
theorem coarse_real_coefficient (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (u y ψ : E) (hu : ‖u‖=1) (huk : u∈K) (hy : ‖y‖≤1) {β : ℝ}
    (hβ : K.starProjection y=β • u) (hov : 1/30<(inner ℂ u ψ).re)
    (herr : ‖y-ψ‖<(1:ℝ)/1000) :
    1/32<β ∧ β≤1 ∧ K.starProjection (y-β • u)=0 := by
  have hPu : K.starProjection u=u := K.starProjection_eq_self_iff.mpr huk
  have hi : (inner ℂ u y).re=β := by
    calc
      (inner ℂ u y).re = (inner ℂ (K.starProjection u) y).re := by rw [hPu]
      _ = (inner ℂ u (K.starProjection y)).re := by rw [K.inner_starProjection_left_eq_right]
      _ = β := by
        rw [hβ,RCLike.real_smul_eq_coe_smul (K := ℂ),inner_smul_right,
          inner_self_eq_norm_sq_to_K,hu]
        simp
  have he : (inner ℂ u ψ).re-β≤‖y-ψ‖ := by
    calc
      (inner ℂ u ψ).re-β = (inner ℂ u (ψ-y)).re := by rw [inner_sub_right,Complex.sub_re,hi]
      _ ≤ ‖inner ℂ u (ψ-y)‖ := Complex.re_le_norm _
      _ ≤ ‖u‖*‖ψ-y‖ := norm_inner_le_norm _ _
      _ = ‖y-ψ‖ := by rw [hu,one_mul,norm_sub_rev]
  have hlo : 1/32<β := by linarith
  refine ⟨hlo,?_,?_⟩
  · have hp := (K.norm_starProjection_apply_le y).trans hy
    rw [hβ,norm_smul,Real.norm_eq_abs,abs_of_pos (by linarith : 0<β),hu,mul_one] at hp
    exact hp
  · have hm : K.starProjection (β • u)=β • K.starProjection u :=
      K.starProjection.toLinearMap.map_smul_of_tower β u
    rw [map_sub,hm,hPu,hβ,sub_self]

variable {S D : Type*} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]

/-- Concrete finite coarse preparation has precisely the real aligned
accepted component required by Proposition4.1. Work-gate/original-oracle
accounting is supplied by the subsequent circuit integration. -/
theorem finite_preparation_coarse_component (s₀ : S) {κ s ŝ α : ℝ}
    (h : BudgetParameters κ s ŝ) (hα : 0<α) (hα2 : α≤2)
    (V : Matrix.unitaryGroup (S × D) ℂ) (hV : star V.val=V.val)
    (H : Matrix D D ℂ) (hH : star H=H) (Ub : Matrix.unitaryGroup D ℂ)
    (i₀ : D) (e : EuclideanSpace ℂ D) (he : ‖e‖=1) (hcol : ∀ i,Ub i i₀=e i)
    (hblock : H=α • signalBlock s₀ V)
    (hprojlo : s^2/(2*κ^2) ≤ ‖kernelProjector H e‖^2)
    (hprojhi : ‖kernelProjector H e‖^2≤s^2/κ^2)
    (hhalf : ‖kernelProjector H e‖^2≤1/2)
    (hZe : ‖Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (matrixPseudoInverse H hH) e‖≤s) :
    let Ψ := finitePreparedState s₀ h hα V Ub i₀ (WithLp.ofLp e)
    let y := WithLp.toLp 2 (zeroAuxiliaryOutput s₀ Ψ)
    let u := normalizedProjectedInput H e
    ‖WithLp.toLp 2 Ψ‖=1 ∧ ∃ β : ℝ, 1/32<β ∧ β≤1 ∧
      kernelProjector H y=β • u ∧ kernelProjector H (y-β • u)=0 := by
  let Ψ := finitePreparedState s₀ h hα V Ub i₀ (WithLp.ofLp e)
  let y := WithLp.toLp 2 (zeroAuxiliaryOutput s₀ Ψ)
  let ψ := WithLp.toLp 2 (preparationOutput H (preparedReflection Ub i₀)
    (overlapMixingParameter κ ŝ) (WithLp.ofLp e))
  let K := LinearMap.ker (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H).toLinearMap
  have hn : ‖WithLp.toLp 2 Ψ‖=1 := (finitePreparedState_norm s₀ h hα V Ub i₀ _).trans he
  refine ⟨hn,?_⟩
  obtain ⟨β,hβ⟩ := lemma49_preparationCompiler s₀ h hα V hV H hH Ub i₀ e he hcol hblock
  have hpn : kernelProjector H e≠0 := by
    intro hz
    rw [hz,norm_zero,zero_pow (by decide : 2≠0)] at hprojlo
    have hspos : 0<s := by linarith [h.scale_ge_one]
    have hp : 0<s^2/(2*κ^2) := by have := h.kappa_pos; positivity
    linarith
  have hu : ‖normalizedProjectedInput H e‖=1 := NormedSpace.norm_normalize hpn
  have huk : normalizedProjectedInput H e∈K :=
    K.smul_of_tower_mem _ (K.starProjection_apply_mem e)
  have hguar := ideal_matrix_guarantees H Ub i₀ e he hcol h.kappa_ge_two h.scale_ge_one
    h.scale_le_kappa h.estimate_lower h.estimate_upper hprojlo hprojhi hhalf
  obtain ⟨c,hc,hw,hf,hs,hfb,hsb,ha,hg,herror⟩ := finite_preparation_error_uniform (D := D) s₀ h hα hα2
  subst c
  have hd := (zeroAuxiliaryOutput_distance s₀ h.layout Ψ
    (preparationOutput H (preparedReflection Ub i₀) (overlapMixingParameter κ ŝ)
      (WithLp.ofLp e))).trans_lt (herror V hV H hH Ub i₀ e he hcol hblock hprojlo hprojhi hhalf hZe)
  have hy : ‖y‖≤1 := (zeroAuxiliaryOutput_norm_le s₀ Ψ).trans_eq hn
  have hb := coarse_real_coefficient K (normalizedProjectedInput H e) y ψ hu huk hy hβ
    hguar.2.2.2.2.1 hd
  exact ⟨β,hb.1,hb.2.1,hβ,hb.2.2⟩

end OptimalQLS.Preparation
