import OptimalQLS.TwoReflectionInverse

noncomputable section
namespace OptimalQLS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def operatorFractionalCatalyst (U : unitary (E →L[ℂ] E)) (r : ℝ) (e : E) : E :=
  Real.sqrt (1-r^2) • Ring.inverse (1-r • (U : E →L[ℂ] E)) e

def operatorFractionalAction (U : unitary (E →L[ℂ] E)) (r : ℝ) : E →L[ℂ] E :=
  ((U : E →L[ℂ] E) - r • 1) * Ring.inverse (1-r • (U : E →L[ℂ] E))

/-- Orthogonal-vector norm calculation behind the exact catalyst cost. -/
theorem fractional_plane_catalyst_norm (U : unitary (E →L[ℂ] E)) (p w : E)
    {r x : ℝ} (hr : |r| < 1) (hx : 0 ≤ x) (hxhalf : x ≤ 1/2)
    (hp : (U : E →L[ℂ] E) p = (1 - 2*x) • p - (2*x) • w)
    (hw : (U : E →L[ℂ] E) w = (2*(1-x)) • p + (1 - 2*x) • w)
    (ho : inner ℂ p w = 0) (hpN : ‖p‖^2 = x) (hwN : ‖w‖^2 = 1-x) :
    ‖operatorFractionalCatalyst U r (p+w)‖^2 =
      (1-r^2) / reflectionPlaneDenominator r x := by
  have hd : reflectionPlaneDenominator r x ≠ 0 :=
    (reflectionPlaneDenominator_pos hr hx hxhalf).ne'
  have hr2 : 0 ≤ 1-r^2 := by nlinarith [(abs_lt.mp hr).1, (abs_lt.mp hr).2]
  have hi : inner ℂ ((1+r) • p) ((1-r) • w) = 0 := by
    simp [inner_smul_left_eq_smul, inner_smul_right_eq_smul, ho]
  rw [operatorFractionalCatalyst, fractional_plane_inverse U p w hr hx hxhalf hp hw,
    norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    mul_pow, mul_pow, sq_abs, sq_abs, Real.sq_sqrt hr2]
  rw [norm_add_sq (𝕜 := ℂ)]
  simp only [hi, RCLike.zero_re, mul_zero, add_zero, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, hpN, hwN]
  have hdform : (1+r)^2*x + (1-r)^2*(1-x) = reflectionPlaneDenominator r x := by
    unfold reflectionPlaneDenominator; ring
  rw [hdform]
  field_simp

/-- The output is also explicitly in the real invariant plane. -/
theorem fractional_plane_output (U : unitary (E →L[ℂ] E)) (p w : E)
    {r x : ℝ} (hr : |r| < 1) (hx : 0 ≤ x) (hxhalf : x ≤ 1/2)
    (hp : (U : E →L[ℂ] E) p = (1 - 2*x) • p - (2*x) • w)
    (hw : (U : E →L[ℂ] E) w = (2*(1-x)) • p + (1 - 2*x) • w) :
    operatorFractionalAction U r (p+w) =
      (((1+r)*(1-2*x-r)+(1-r)*(2*(1-x))) / reflectionPlaneDenominator r x) • p +
      (((1-r)*(1-2*x-r)-(1+r)*(2*x)) / reflectionPlaneDenominator r x) • w := by
  have hlin (a : ℝ) (v : E) : (U : E →L[ℂ] E) (a • v) = a • (U : E →L[ℂ] E) v :=
    (U : E →L[ℂ] E).toLinearMap.map_smul_of_tower a v
  rw [operatorFractionalAction, ContinuousLinearMap.mul_apply,
    fractional_plane_inverse U p w hr hx hxhalf hp hw]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, hlin, map_add, hp, hw]
  simp only [div_eq_mul_inv]
  module

/-- The actual fractional action is unitary in the continuous-operator algebra. -/
theorem operatorFractionalAction_unitary (U : unitary (E →L[ℂ] E))
    {r : ℝ} (hr : |r| < 1) : operatorFractionalAction U r ∈ unitary (E →L[ℂ] E) := by
  let N := (U : E →L[ℂ] E) - r • 1
  let D := 1 - r • (U : E →L[ℂ] E)
  have hD := unitary_fractional_denominator_isUnit U hr
  have hU : star (U : E →L[ℂ] E) * U = 1 := U.property.1
  have hg : star N * N = star D * D := by
    dsimp [N,D]
    simp only [star_sub, star_smul, star_trivial, star_one, sub_mul, mul_sub,
      one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hU]
    module
  have hi : star (N * Ring.inverse D) * (N * Ring.inverse D) = 1 := by
    rw [star_mul]
    calc
      _ = star (Ring.inverse D) * (star N * N) * Ring.inverse D := by simp [mul_assoc]
      _ = star (Ring.inverse D) * (star D * D) * Ring.inverse D := by rw [hg]
      _ = 1 := by
        rw [mul_assoc, mul_assoc, Ring.mul_inverse_cancel _ hD, mul_one,
          ← star_mul, Ring.mul_inverse_cancel _ hD, star_one]
  have hi' : (N * Ring.inverse D) * star (N * Ring.inverse D) = 1 := by
    have hnD : N * D = D * N := by
      dsimp [N,D]
      simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
      module
    have hright : N * star N = D * star D := by
      have hu : (U : E →L[ℂ] E) * star (U : E →L[ℂ] E) = 1 := U.property.2
      dsimp [N,D]
      simp only [star_sub, star_smul, star_trivial, star_one, sub_mul, mul_sub,
        one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hu]
      module
    have hcomm : N * Ring.inverse D = Ring.inverse D * N := by
      calc
        N * Ring.inverse D = (Ring.inverse D * D) * N * Ring.inverse D := by
          rw [Ring.inverse_mul_cancel _ hD, one_mul]
        _ = Ring.inverse D * (D * N) * Ring.inverse D := by simp only [mul_assoc]
        _ = Ring.inverse D * (N * D) * Ring.inverse D := by rw [← hnD]
        _ = Ring.inverse D * N * (D * Ring.inverse D) := by simp only [mul_assoc]
        _ = Ring.inverse D * N := by rw [Ring.mul_inverse_cancel _ hD, mul_one]
    rw [hcomm, star_mul]
    calc
      _ = Ring.inverse D * (N * star N) * star (Ring.inverse D) := by simp [mul_assoc]
      _ = Ring.inverse D * (D * star D) * star (Ring.inverse D) := by rw [hright]
      _ = 1 := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hD, one_mul,
        ← star_mul, Ring.inverse_mul_cancel _ hD, star_one]
  exact ⟨hi,hi'⟩

end OptimalQLS
