import OptimalQLS.TwoReflections
import Mathlib.Analysis.Normed.Ring.Units

noncomputable section
namespace OptimalQLS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def reflectionPlaneDenominator (r x : ℝ) : ℝ := 1 + r^2 - 2*r*(1-2*x)

theorem reflectionPlaneDenominator_pos {r x : ℝ} (hr : |r| < 1)
    (hx : 0 ≤ x) (hxhalf : x ≤ 1/2) : 0 < reflectionPlaneDenominator r x := by
  have hp : 0 < (1-r)^2 * (1-x) := mul_pos (sq_pos_of_pos (by linarith [(abs_lt.mp hr).2])) (by linarith)
  have hn : 0 ≤ (1+r)^2 * x := mul_nonneg (sq_nonneg _) hx
  unfold reflectionPlaneDenominator
  nlinarith

/-- Unit-norm preservation establishes Neumann invertibility for the actual
unitary operator, including arbitrary finite Hilbert-space coordinates. -/
theorem unitary_fractional_denominator_isUnit (U : unitary (E →L[ℂ] E))
    {r : ℝ} (hr : |r| < 1) : IsUnit (1 - r • (U : E →L[ℂ] E)) := by
  have hu : ‖(U : E →L[ℂ] E)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    rw [ContinuousLinearMap.norm_map_of_mem_unitary U.property, one_mul]
  apply isUnit_one_sub_of_norm_lt_one
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left hu (abs_nonneg r)).trans_lt (by simpa using hr)

/-- The inverse is a concrete real linear combination of Pe and (I-P)e. -/
theorem fractional_plane_inverse (U : unitary (E →L[ℂ] E)) (p w : E)
    {r x : ℝ} (hr : |r| < 1) (hx : 0 ≤ x) (hxhalf : x ≤ 1/2)
    (hp : (U : E →L[ℂ] E) p = (1 - 2*x) • p - (2*x) • w)
    (hw : (U : E →L[ℂ] E) w = (2*(1-x)) • p + (1 - 2*x) • w) :
    Ring.inverse (1 - r • (U : E →L[ℂ] E)) (p+w) =
      (reflectionPlaneDenominator r x)⁻¹ • ((1+r) • p + (1-r) • w) := by
  let D := 1 - r • (U : E →L[ℂ] E)
  let d := reflectionPlaneDenominator r x
  let v := d⁻¹ • ((1+r) • p + (1-r) • w)
  have hd : d ≠ 0 := (reflectionPlaneDenominator_pos hr hx hxhalf).ne'
  have hlin (a : ℝ) (v : E) : (U : E →L[ℂ] E) (a • v) = a • (U : E →L[ℂ] E) v :=
    (U : E →L[ℂ] E).toLinearMap.map_smul_of_tower a v
  have hDv : D v = p+w := by
    dsimp only [D, v, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.smul_apply]
    rw [hlin, map_add, hlin, hlin, hp, hw]
    have hc₁ : (1+r) - r*((1+r)*(1-2*x) + (1-r)*(2*(1-x))) = d := by
      dsimp [d, reflectionPlaneDenominator]; ring
    have hc₂ : (1-r) - r*(-(1+r)*(2*x) + (1-r)*(1-2*x)) = d := by
      dsimp [d, reflectionPlaneDenominator]; ring
    calc
      _ = (d⁻¹ * ((1+r) - r*((1+r)*(1-2*x)+(1-r)*(2*(1-x))))) • p +
          (d⁻¹ * ((1-r) - r*(-(1+r)*(2*x)+(1-r)*(1-2*x)))) • w := by module
      _ = p+w := by rw [hc₁,hc₂,inv_mul_cancel₀ hd]; simp
  have hD := unitary_fractional_denominator_isUnit U hr
  have hh := congrArg (fun z : E => Ring.inverse D z) hDv
  have hInv : Ring.inverse D (D v) = v := by
    change (Ring.inverse D * D) v = v
    rw [Ring.inverse_mul_cancel _ hD]
    rfl
  change Ring.inverse D (D v) = Ring.inverse D (p+w) at hh
  rw [hInv] at hh
  exact hh.symm

end OptimalQLS
