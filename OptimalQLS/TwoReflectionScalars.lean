import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Exact real arithmetic for the two-reflection transducer -/
noncomputable section
namespace OptimalQLS

def overlapMixingParameter (κ ŝ : ℝ) : ℝ := (κ - 16 * ŝ) / (κ + 16 * ŝ)

theorem overlapMixingParameter_mem {κ ŝ : ℝ} (hκ : 0 < κ) (hs : 0 < ŝ) :
    -1 < overlapMixingParameter κ ŝ ∧ overlapMixingParameter κ ŝ < 1 := by
  have hd : 0 < κ + 16 * ŝ := by positivity
  unfold overlapMixingParameter
  constructor
  · apply (lt_div_iff₀ hd).mpr; nlinarith
  · apply (div_lt_iff₀ hd).mpr; nlinarith

/-- The exact denominator after substituting the supplied classical estimate. -/
theorem overlap_denominator_identity {κ ŝ x : ℝ} (hκ : 0 < κ) (hs : 0 < ŝ) :
    1 + (overlapMixingParameter κ ŝ)^2 -
      2 * overlapMixingParameter κ ŝ * (1 - 2 * x) =
      4 * ((16 * ŝ)^2 * (1 - x) + κ^2 * x) / (κ + 16 * ŝ)^2 := by
  have hd : κ + 16 * ŝ ≠ 0 := by positivity
  unfold overlapMixingParameter
  field_simp
  ring

/-- Exact catalyst squared norm, with an explicit and uniform constant. -/
theorem overlap_catalyst_cost {κ ŝ x : ℝ} (hκ : 0 < κ) (hs : 0 < ŝ)
    (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    (1 - (overlapMixingParameter κ ŝ)^2) /
      (1 + (overlapMixingParameter κ ŝ)^2 -
        2 * overlapMixingParameter κ ŝ * (1 - 2 * x)) =
      16 * κ * ŝ / ((16 * ŝ)^2 * (1 - x) + κ^2 * x) ∧
    16 * κ * ŝ / ((16 * ŝ)^2 * (1 - x) + κ^2 * x) ≤ κ / (8 * ŝ) := by
  have hd : 0 < κ + 16 * ŝ := by positivity
  have hden : 0 < (16 * ŝ)^2 * (1 - x) + κ^2 * x := by
    have : 0 < (16 * ŝ)^2 * (1 - x) := mul_pos (sq_pos_of_pos (by positivity)) (by linarith)
    positivity
  constructor
  · rw [overlap_denominator_identity hκ hs]
    unfold overlapMixingParameter
    field_simp
    ring
  · apply (div_le_div_iff₀ hden (by positivity : 0 < 8 * ŝ)).mpr
    have ht : 0 ≤ κ^2 * x := mul_nonneg (sq_nonneg _) hx
    have hs2 : 0 < ŝ^2 := sq_pos_of_pos hs
    have hb : 128 * ŝ^2 ≤ (16 * ŝ)^2 * (1 - x) + κ^2 * x := by
      nlinarith [mul_nonneg (sq_nonneg ŝ) (show 0 ≤ 1 / 2 - x by linarith)]
    have hh := mul_le_mul_of_nonneg_left hb hκ.le
    nlinarith

/-- The rational overlap estimate avoids trigonometric inverses entirely.
These are exactly the squared-tangent bounds derived from the supplied estimate. -/
theorem overlap_from_squared_tangent {γ c t : ℝ}
    (hγ : 0 ≤ γ) (hc : 0 ≤ c) (hcircle : γ^2 + c^2 = 1)
    (ht : 0 ≤ t) (htlo : 1 / 3200 ≤ t^2) (hthi : t^2 ≤ 1 / 18) :
    1 / 30 < (γ * (1 - t^2) + 2 * c * t) / (1 + t^2) := by
  have htquarter : t ≤ 1 / 4 := by nlinarith
  have hγ1 : γ ≤ 1 := by nlinarith [sq_nonneg c]
  have hc1 : c ≤ 1 := by nlinarith [sq_nonneg γ]
  have hgc : 1 ≤ γ + c := by nlinarith [mul_nonneg hγ hc]
  have hpoly : 0 ≤ 1 - t^2 - 2 * t := by nlinarith
  have hdiff : 0 ≤ γ * (1 - t^2) - 2 * t * (1 - c) := by
    have hh := mul_nonneg hγ hpoly
    have hh' := mul_le_mul_of_nonneg_left (show 1 - c ≤ γ by linarith) (by positivity : 0 ≤ 2*t)
    nlinarith
  have htstrong : 19 / 1080 < t := by nlinarith
  have hden : 0 < 1 + t^2 := by positivity
  apply (lt_div_iff₀ hden).mpr
  nlinarith

/-- Exact squared tangent bounds from the original κ,s,ŝ and projection promises. -/
theorem overlap_squared_tangent_bounds {κ s ŝ γ c : ℝ}
    (hκ : 0 < κ) (hs : 0 < s) (hshlo : 3*s/8 ≤ ŝ) (hshhi : ŝ ≤ 5*s/2)
    (hγ : 0 < γ) (hc : 0 < c) (hcircle : γ^2 + c^2 = 1)
    (hγlo : s^2 / (2*κ^2) ≤ γ^2) (hγhi : γ^2 ≤ s^2/κ^2)
    (hγhalf : γ^2 ≤ 1/2) :
    1/3200 ≤ (κ*γ/(16*ŝ*c))^2 ∧ (κ*γ/(16*ŝ*c))^2 ≤ 1/18 := by
  have hsh : 0 < ŝ := by nlinarith
  have hk2 : 0 < κ^2 := sq_pos_of_pos hκ
  have hs2 : 0 < s^2 := sq_pos_of_pos hs
  have hden : 0 < (16*ŝ*c)^2 := sq_pos_of_pos (by positivity)
  have hnumlo : s^2 / 2 ≤ κ^2 * γ^2 := by
    have hh := (div_le_iff₀ (by positivity : 0 < 2*κ^2)).mp hγlo
    nlinarith
  have hnumhi : κ^2 * γ^2 ≤ s^2 := by
    have hh := (le_div_iff₀ hk2).mp hγhi
    nlinarith
  have hsh2lo : 9*s^2/64 ≤ ŝ^2 := by nlinarith
  have hsh2hi : ŝ^2 ≤ 25*s^2/4 := by nlinarith
  have hc2lo : 1/2 ≤ c^2 := by nlinarith
  have hc2hi : c^2 ≤ 1 := by nlinarith [sq_nonneg γ]
  have hdlo : 18*s^2 ≤ (16*ŝ*c)^2 := by
    have h₁ := mul_le_mul_of_nonneg_right hsh2lo (sq_nonneg c)
    have h₂ := mul_le_mul_of_nonneg_left hc2lo (by positivity : 0 ≤ 9*s^2/64)
    nlinarith
  have hdhi : (16*ŝ*c)^2 ≤ 1600*s^2 := by
    have h₁ := mul_le_mul_of_nonneg_right hsh2hi (sq_nonneg c)
    have h₂ := mul_le_mul_of_nonneg_left hc2hi (by positivity : 0 ≤ 25*s^2/4)
    nlinarith
  rw [div_pow, mul_pow]
  constructor
  · apply (le_div_iff₀ hden).mpr
    nlinarith
  · apply (div_le_iff₀ hden).mpr
    nlinarith

/-- Half-angle parameter obtained by substituting the known mixing ratio. -/
theorem overlap_tangent_substitution {κ ŝ γ c : ℝ} (hκ : 0 < κ) (hs : 0 < ŝ)
    (hc : c ≠ 0) :
    (1 + overlapMixingParameter κ ŝ) * γ /
      ((1 - overlapMixingParameter κ ŝ) * c) = κ * γ / (16 * ŝ * c) := by
  have hd : κ + 16 * ŝ ≠ 0 := by positivity
  have hs' : ŝ ≠ 0 := hs.ne'
  unfold overlapMixingParameter
  field_simp
  <;> ring

/-- The exact overlap formula in rational half-angle coordinates. -/
theorem overlap_half_angle_identity {r γ c : ℝ} (hr : |r| < 1) (hc : 0 < c)
    (hcircle : γ^2 + c^2 = 1) :
    let t := (1+r)*γ/((1-r)*c)
    γ * (((1+r)*(1-2*γ^2-r)+(1-r)*(2*(1-γ^2))) /
      (1+r^2-2*r*(1-2*γ^2))) = (γ*(1-t^2)+2*c*t)/(1+t^2) := by
  dsimp only
  have hb : 0 < 1-r := by linarith [(abs_lt.mp hr).2]
  have hbc : (1-r)*c ≠ 0 := (mul_pos hb hc).ne'
  have hdpos : 0 < (1-r)^2*c^2+(1+r)^2*γ^2 := by
    have hp : 0 < (1-r)^2*c^2 := mul_pos (sq_pos_of_pos hb) (sq_pos_of_pos hc)
    have hn : 0 ≤ (1+r)^2*γ^2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    linarith
  have hc2 : c^2 = 1-γ^2 := by linarith
  have hdeq : 1+r^2-2*r*(1-2*γ^2) = (1-r)^2*c^2+(1+r)^2*γ^2 := by
    rw [hc2]; ring
  have hd : 1+r^2-2*r*(1-2*γ^2) ≠ 0 := by rw [hdeq]; exact hdpos.ne'
  have htn : 1+((1+r)*γ/((1-r)*c))^2 ≠ 0 := by positivity
  have hratio : (γ*(1-((1+r)*γ/((1-r)*c))^2)+
      2*c*((1+r)*γ/((1-r)*c))) / (1+((1+r)*γ/((1-r)*c))^2) =
      γ*((1-r)^2*c^2-(1+r)^2*γ^2+2*(1+r)*(1-r)*c^2) /
        ((1-r)^2*c^2+(1+r)^2*γ^2) := by
    field_simp
    <;> ring
  rw [hratio, hdeq, mul_div_assoc]
  congr 1
  rw [hc2]
  ring

end OptimalQLS
