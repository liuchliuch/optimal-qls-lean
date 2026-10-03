import OptimalQLS.LowerBounds.VectorPerturbationScalars

/-! Concrete norm-adjustment coefficients and the5/9 history mass in6.4. -/
noncomputable section
namespace OptimalQLS.LowerBounds

def adjustedSolutionScale (estimate Y : ℝ) : ℝ := min (3 * estimate / 2) Y

def identitySourceCoefficient (Y s : ℝ) : ℝ := Real.sqrt ((Y ^ 2 - s ^ 2) / (Y ^ 2 - 1))
def historySourceCoefficient (Y s : ℝ) : ℝ := Real.sqrt ((s ^ 2 - 1) / (Y ^ 2 - 1))

theorem adjustedSolutionScale_bounds {kappa estimate Y : ℝ} (hk : 4 ≤ kappa)
    (he : 1 ≤ estimate) (hek : estimate ≤ kappa) (hY : kappa / 2 ≤ Y) :
    estimate / 2 ≤ adjustedSolutionScale estimate Y ∧
      adjustedSolutionScale estimate Y ≤ 3 * estimate / 2 ∧
      3 / 2 ≤ adjustedSolutionScale estimate Y ∧ adjustedSolutionScale estimate Y ≤ Y := by
  unfold adjustedSolutionScale
  refine ⟨le_min (by linarith) (by linarith), min_le_left _ _, ?_, min_le_right _ _⟩
  exact le_min (by linarith) (by linarith)

@[simp] theorem identitySourceCoefficient_nonneg (Y s : ℝ) : 0 ≤ identitySourceCoefficient Y s :=
  Real.sqrt_nonneg _
@[simp] theorem historySourceCoefficient_nonneg (Y s : ℝ) : 0 ≤ historySourceCoefficient Y s :=
  Real.sqrt_nonneg _

theorem adjustment_denominator_pos {Y s : ℝ} (hs : 3 / 2 ≤ s) (hsY : s ≤ Y) : 0 < Y ^ 2 - 1 := by
  nlinarith

theorem identitySourceCoefficient_sq {Y s : ℝ} (hs : 3 / 2 ≤ s) (hsY : s ≤ Y) :
    identitySourceCoefficient Y s ^ 2 = (Y ^ 2 - s ^ 2) / (Y ^ 2 - 1) := by
  apply Real.sq_sqrt
  apply div_nonneg _ (adjustment_denominator_pos hs hsY).le
  nlinarith

theorem historySourceCoefficient_sq {Y s : ℝ} (hs : 3 / 2 ≤ s) (hsY : s ≤ Y) :
    historySourceCoefficient Y s ^ 2 = (s ^ 2 - 1) / (Y ^ 2 - 1) := by
  apply Real.sq_sqrt
  exact div_nonneg (by nlinarith) (adjustment_denominator_pos hs hsY).le

/-- The actual source coefficient squares sum to one. -/
theorem adjustment_source_identity {Y s : ℝ} (hs : 3 / 2 ≤ s) (hsY : s ≤ Y) :
    identitySourceCoefficient Y s ^ 2 + historySourceCoefficient Y s ^ 2 = 1 := by
  rw [identitySourceCoefficient_sq hs hsY, historySourceCoefficient_sq hs hsY]
  field_simp [(adjustment_denominator_pos hs hsY).ne']
  ring

/-- Applying the history inverse gives exactly the requested adjusted norm. -/
theorem adjustment_solution_identity {Y s : ℝ} (hs : 3 / 2 ≤ s) (hsY : s ≤ Y) :
    identitySourceCoefficient Y s ^ 2 + Y ^ 2 * historySourceCoefficient Y s ^ 2 = s ^ 2 := by
  rw [identitySourceCoefficient_sq hs hsY, historySourceCoefficient_sq hs hsY]
  field_simp [(adjustment_denominator_pos hs hsY).ne']
  ring

/-- The normalized adjusted solution retains at least5/9 of its mass in the
history summand. This is the concrete source-mixture calculation in6.4. -/
theorem adjusted_history_mass_lower {Y s : ℝ} (hs : 3 / 2 ≤ s) (hsY : s ≤ Y) :
    (5 / 9 : ℝ) ≤ historySourceCoefficient Y s ^ 2 * Y ^ 2 / s ^ 2 := by
  have hd := adjustment_denominator_pos hs hsY
  have hs2 : 0 < s ^ 2 := by nlinarith
  have hpoly : 0 ≤ (4 * s ^ 2 - 9) * Y ^ 2 := by
    apply mul_nonneg _ (sq_nonneg Y)
    nlinarith
  rw [historySourceCoefficient_sq hs hsY]
  apply (le_div_iff₀ hs2).mpr
  have heq : (s ^ 2 - 1) / (Y ^ 2 - 1) * Y ^ 2 =
      ((s ^ 2 - 1) * Y ^ 2) / (Y ^ 2 - 1) := by ring
  rw [heq]
  apply (le_div_iff₀ hd).mpr
  nlinarith

end OptimalQLS.LowerBounds
