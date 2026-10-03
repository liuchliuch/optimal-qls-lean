import OptimalQLS.TwoReflectionProjection
import Mathlib.LinearAlgebra.Span.Basic

/-! # Lemma 4.7 from the actual orthogonal projector and unitary reflections -/
noncomputable section
namespace OptimalQLS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Explicit-constant form of the entire two-reflection lemma. The catalyst
and output are the literal fractional action of the actual two reflections. -/
theorem lemma47 (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (e : E) (he : ‖e‖ = 1) {κ s ŝ : ℝ}
    (hκ : 2 ≤ κ) (hs : 1 ≤ s) (hsκ : s ≤ κ)
    (hshlo : 3*s/8 ≤ ŝ) (hshhi : ŝ ≤ 5*s/2)
    (hprojlo : s^2/(2*κ^2) ≤ ‖K.starProjection e‖^2)
    (hprojhi : ‖K.starProjection e‖^2 ≤ s^2/κ^2)
    (hprojhalf : ‖K.starProjection e‖^2 ≤ 1/2) :
    let U := kernelMixingUnitary K e he
    let r := overlapMixingParameter κ ŝ
    let q := operatorFractionalCatalyst U r e
    let ψ := operatorFractionalAction U r e
    (-1 < r ∧ r < 1 ∧ ‖ψ‖ = 1 ∧
    (inner ℂ (NormedSpace.normalize (K.starProjection e)) ψ).im = 0 ∧
    1/30 < (inner ℂ (NormedSpace.normalize (K.starProjection e)) ψ).re ∧
    q ∈ Submodule.span ℝ ({K.starProjection e, e-K.starProjection e} : Set E) ∧
    ‖q‖^2 ≤ κ/(8*ŝ) ∧ κ/(8*ŝ) ≤ κ/(3*s)) := by
  let U := kernelMixingUnitary K e he
  let r := overlapMixingParameter κ ŝ
  let p := K.starProjection e
  let w := e-p
  let q := operatorFractionalCatalyst U r e
  let ψ := operatorFractionalAction U r e
  let γ := ‖p‖
  let c := ‖w‖
  let x := γ^2
  have hκ0 : 0 < κ := by linarith
  have hs0 : 0 < s := by linarith
  have hsh0 : 0 < ŝ := by nlinarith
  have hrbounds : -1 < r ∧ r < 1 := overlapMixingParameter_mem hκ0 hsh0
  have hr : |r| < 1 := abs_lt.mpr hrbounds
  obtain ⟨ho,hn,hep,hew⟩ := kernelProjection_plane_data K e he
  have hepw : e = p+w := by dsimp [w]; abel
  have hcircle : γ^2+c^2=1 := hn
  have hγ0 : 0 < γ := by
    have hh : 0 < s^2/(2*κ^2) := by positivity
    have : 0 < γ^2 := hh.trans_le hprojlo
    have : 0 ≤ γ := norm_nonneg p
    nlinarith
  have hc0 : 0 < c := by
    have : 0 ≤ c := norm_nonneg w
    nlinarith [hprojhalf]
  have hpn : p ≠ 0 := norm_pos_iff.mp hγ0
  have hx : 0 ≤ x := sq_nonneg γ
  have hxhalf : x ≤ 1/2 := hprojhalf
  have hwN : ‖w‖^2=1-x := by dsimp only [x,c,γ] at *; linarith
  obtain ⟨hp,hw⟩ := kernelMixingUnitary_plane K e he
  have houtput : ψ =
      (((1+r)*(1-2*x-r)+(1-r)*(2*(1-x))) / reflectionPlaneDenominator r x) • p +
      (((1-r)*(1-2*x-r)-(1+r)*(2*x)) / reflectionPlaneDenominator r x) • w := by
    change operatorFractionalAction U r e = _
    rw [hepw]
    exact fractional_plane_output U p w hr hx hxhalf hp hw
  have hinner := normalized_projection_overlap p w hpn ho
    (((1+r)*(1-2*x-r)+(1-r)*(2*(1-x))) / reflectionPlaneDenominator r x)
    (((1-r)*(1-2*x-r)-(1+r)*(2*x)) / reflectionPlaneDenominator r x)
  rw [← houtput] at hinner
  let t := (1+r)*γ/((1-r)*c)
  have ht : t = κ*γ/(16*ŝ*c) := overlap_tangent_substitution hκ0 hsh0 hc0.ne'
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have htbd : 1/3200 ≤ t^2 ∧ t^2 ≤ 1/18 := by
    rw [ht]
    exact overlap_squared_tangent_bounds hκ0 hs0 hshlo hshhi hγ0 hc0 hcircle
      hprojlo hprojhi hprojhalf
  have hang := overlap_half_angle_identity hr hc0 hcircle
  have houtreal : 1/30 <
      (((1+r)*(1-2*x-r)+(1-r)*(2*(1-x))) / reflectionPlaneDenominator r x) * γ := by
    rw [mul_comm]
    change 1/30 < γ * (((1+r)*(1-2*γ^2-r)+(1-r)*(2*(1-γ^2))) /
      (1+r^2-2*r*(1-2*γ^2)))
    rw [hang]
    exact overlap_from_squared_tangent hγ0.le hc0.le hcircle ht0 htbd.1 htbd.2
  have hcosteq : ‖q‖^2 = (1-r^2)/reflectionPlaneDenominator r x := by
    change ‖operatorFractionalCatalyst U r e‖^2 = _
    rw [hepw]
    exact fractional_plane_catalyst_norm U p w hr hx hxhalf hp hw ho rfl hwN
  have hcost : ‖q‖^2 ≤ κ/(8*ŝ) := by
    rw [hcosteq]
    exact (overlap_catalyst_cost hκ0 hsh0 hx hxhalf).1.trans_le
      (overlap_catalyst_cost hκ0 hsh0 hx hxhalf).2
  change -1 < r ∧ r < 1 ∧ ‖ψ‖ = 1 ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  refine ⟨hrbounds.1,hrbounds.2,?_,?_,?_,?_,hcost,?_⟩
  · exact (ContinuousLinearMap.norm_map_of_mem_unitary (operatorFractionalAction_unitary U hr) e).trans he
  · rw [hinner]; rfl
  · rw [hinner]; exact houtreal
  · let L := Submodule.span ℝ ({p,w} : Set E)
    have hpmem : p ∈ L := Submodule.subset_span (by simp)
    have hwmem : w ∈ L := Submodule.subset_span (by simp)
    change operatorFractionalCatalyst U r e ∈ L
    rw [operatorFractionalCatalyst, hepw, fractional_plane_inverse U p w hr hx hxhalf hp hw]
    exact L.smul_mem _ (L.smul_mem _ (L.add_mem (L.smul_mem _ hpmem) (L.smul_mem _ hwmem)))
  · apply div_le_div_of_nonneg_left hκ0.le (by positivity : 0 < 3*s)
    nlinarith

end OptimalQLS
