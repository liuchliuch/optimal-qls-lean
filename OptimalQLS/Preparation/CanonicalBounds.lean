import OptimalQLS.Preparation.Canonical

noncomputable section
namespace OptimalQLS.Preparation
open Matrix TransducerCompiler
variable {S D : Type*} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]

/-- The actual canonical catalyst satisfies all Appendix A.2 budgets. The
projection and inverse bounds here are the concrete auxiliary-matrix geometry
promises; no transducer cost or catalyst certificate is assumed. -/
theorem canonical_energy_bounds (s₀ : S)
    (V : Matrix.unitaryGroup (S × D) ℂ) (hV : star (V : Matrix (S × D) (S × D) ℂ)=V)
    (H : Matrix D D ℂ) (hH : star H=H) (Ub : Matrix.unitaryGroup D ℂ)
    (i₀ : D) (e : EuclideanSpace ℂ D) (he : ‖e‖=1) (hcol : ∀ i, Ub i i₀=e i)
    {κ s ŝ α : ℝ} (hκ : 2≤κ) (hs : 1≤s) (hsκ : s≤κ)
    (hshlo : 3*s/8≤ŝ) (hshhi : ŝ≤5*s/2) (hα : 0<α) (hα2 : α≤2)
    (hblock : H=α • signalBlock s₀ V)
    (hprojlo : s^2/(2*κ^2) ≤
      ‖(LinearMap.ker (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H).toLinearMap).starProjection e‖^2)
    (hprojhi : ‖(LinearMap.ker (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H).toLinearMap).starProjection e‖^2≤s^2/κ^2)
    (hhalf : ‖(LinearMap.ker (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H).toLinearMap).starProjection e‖^2≤1/2)
    (hZe : ‖Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (matrixPseudoInverse H hH) e‖≤s) :
    let r := overlapMixingParameter κ ŝ
    let q := preparationQ H (preparedReflection Ub i₀) r (WithLp.ofLp e)
    energy (preparationFirst s₀ V H hH α ŝ q)<8*κ ∧
    energy (preparationInternal s₀ q)+energy (preparationFirst s₀ V H hH α ŝ q)+
      energy (preparationSecond s₀ H q)<9*κ ∧
    energy (preparationSecond s₀ H q)≤κ/(8*ŝ) := by
  let K := LinearMap.ker (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H).toLinearMap
  let r := overlapMixingParameter κ ŝ
  let q := preparationQ H (preparedReflection Ub i₀) r (WithLp.ofLp e)
  have h := ideal_matrix_guarantees H Ub i₀ e he hcol hκ hs hsκ hshlo hshhi hprojlo hprojhi hhalf
  dsimp only at h
  obtain ⟨hrlo,hrhi,hψ,him,hov,hspan,hq,hq'⟩ := h
  have hτ : 0<ŝ := by linarith
  have hc := preparation_plane_costs K e he
    (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (matrixPseudoInverse H hH))
    (matrixPseudoInverse_kills_projection H hH e) (by linarith : 0<κ) hs hshlo hshhi hα hα2
    hZe hhalf (WithLp.toLp 2 q) hspan (le_trans hq hq')
  dsimp only
  change energy (preparationFirst s₀ V H hH α ŝ q)<8*κ ∧
    energy (preparationInternal s₀ q)+energy (preparationFirst s₀ V H hH α ŝ q)+
      energy (preparationSecond s₀ H q)<9*κ ∧
    energy (preparationSecond s₀ H q)≤κ/(8*ŝ)
  rw [preparationFirst_energy s₀ V hV H hH hα hτ hblock,
    preparationInternal_energy,preparationSecond_energy,energy_eq_norm_sq]
  refine ⟨hc.1,?_,hq⟩
  nlinarith [hc.2]

end OptimalQLS.Preparation
