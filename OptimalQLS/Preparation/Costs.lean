import Mathlib.Tactic

/-! # Explicit separate catalyst budgets for preparation -/
namespace OptimalQLS.Preparation

/-- The two orthogonal plane weights give the simultaneous catalyst costs.
This scalar bound is used after the concrete vector weights have been proved. -/
theorem preparation_cost_bounds {κ s ŝ α P R Z : ℝ}
    (hκ : 0 < κ) (hs : 1 ≤ s) (hshlo : 3*s/8 ≤ ŝ) (hshhi : ŝ ≤ 5*s/2)
    (hα : 0 < α) (hα2 : α ≤ 2) (hP : 0 ≤ P) (hR : 0 ≤ R)
    (hZ : 0 ≤ Z) (hZbd : Z ≤ 2*s^2*R)
    (hQ : P+R ≤ κ/(3*s)) :
    2*α*(ŝ*P+Z/ŝ) < 8*κ ∧ 2*α*(ŝ*P+Z/ŝ)+2*(P+R) < 9*κ := by
  have hs0 : 0 < s := by linarith
  have hsh : 0 < ŝ := by nlinarith
  have hco : 2*s^2/ŝ ≤ 16*s/3 := by
    apply (div_le_iff₀ hsh).mpr
    nlinarith [mul_le_mul_of_nonneg_left hshlo hs0.le]
  have hpco : ŝ ≤ 16*s/3 := by linarith
  have hinside : ŝ*P+Z/ŝ ≤ (16*s/3)*(P+R) := by
    have hz' : Z/ŝ ≤ (2*s^2/ŝ)*R := by
      calc
        _ ≤ (2*s^2*R)/ŝ := div_le_div_of_nonneg_right hZbd hsh.le
        _ = _ := by ring
    have h₁ := mul_le_mul_of_nonneg_right hpco hP
    have h₂ := mul_le_mul_of_nonneg_right hco hR
    nlinarith
  have hi0 : 0 ≤ ŝ*P+Z/ŝ := by positivity
  have hL : 2*α*(ŝ*P+Z/ŝ) ≤ (64*s/3)*(P+R) := by
    have ha := mul_le_mul_of_nonneg_right hα2 hi0
    nlinarith
  have hLκ : 2*α*(ŝ*P+Z/ŝ) ≤ (64/9)*κ := by
    have hh := mul_le_mul_of_nonneg_left hQ (by positivity : 0 ≤ 64*s/3)
    have hc : (64*s/3)*(κ/(3*s))=(64/9)*κ := by field_simp; ring
    rw [hc] at hh
    exact hL.trans hh
  have hQκ : P+R ≤ κ/3 := by
    have hh : κ/(3*s) ≤ κ/3 :=
      div_le_div_of_nonneg_left hκ.le (by norm_num) (by nlinarith)
    exact hQ.trans hh
  constructor <;> nlinarith

end OptimalQLS.Preparation
