import OptimalQLS.LowerBounds.SourceRotation

/-! Concrete small full-oracle perturbation for Lemma6.5. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
variable {D : Type*} [Fintype D] [DecidableEq D]

def perturbationCos (tau : ℝ) : ℝ := (Real.sqrt (1 + tau ^ 2))⁻¹

def perturbationSin (tau : ℝ) : ℝ := tau * perturbationCos tau

theorem perturbation_trigonometry (tau : ℝ) : perturbationCos tau ^ 2 + perturbationSin tau ^ 2 = 1 := by
  have hp : 0 < 1 + tau ^ 2 := by positivity
  have hs := Real.sq_sqrt hp.le
  have hn := Real.sqrt_ne_zero'.mpr hp
  simp only [perturbationSin, perturbationCos]
  field_simp
  nlinarith

theorem perturbation_coefficient_bounds {tau : ℝ} (ht : 0 ≤ tau) :
    0 ≤ perturbationCos tau ∧ perturbationCos tau ≤ 1 ∧
    0 ≤ perturbationSin tau ∧ perturbationSin tau ≤ tau ∧
    1 - perturbationCos tau ≤ tau := by
  have hd : 0 < Real.sqrt (1 + tau ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ 1 + tau ^ 2 by positivity)
  have hd1 : 1 ≤ Real.sqrt (1 + tau ^ 2) := by nlinarith
  have hdhi : Real.sqrt (1 + tau ^ 2) ≤ 1 + tau := by nlinarith
  have hc0 : 0 ≤ perturbationCos tau := by unfold perturbationCos; positivity
  have hc1 : perturbationCos tau ≤ 1 := by
    unfold perturbationCos
    exact inv_le_one_of_one_le₀ hd1
  refine ⟨hc0, hc1, mul_nonneg ht hc0, mul_le_of_le_one_right ht hc1, ?_⟩
  have hclo : 1 - tau ≤ (Real.sqrt (1 + tau ^ 2))⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ hd).mpr
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hd1)]
  change 1 - tau ≤ perturbationCos tau at hclo
  linarith

/-- The literal normalized nearby source. -/
def perturbedSource (b e : D → ℂ) (tau : ℝ) : D → ℂ :=
  perturbationCos tau • (b + tau • e)

def perturbationRotation (b e : D → ℂ) (h : OrthogonalUnitPair b e) (tau : ℝ) : Matrix.unitaryGroup D ℂ :=
  sourceRotationUnitary b e h (perturbationCos tau) (perturbationSin tau) (perturbation_trigonometry tau)

theorem perturbationRotation_prepares (b e : D → ℂ) (h : OrthogonalUnitPair b e) (tau : ℝ) :
    (perturbationRotation b e h tau : Matrix D D ℂ) *ᵥ b = perturbedSource b e tau := by
  change sourcePlaneRotation b e (perturbationCos tau) (perturbationSin tau) *ᵥ b = _
  rw [sourcePlaneRotation_prepares b e h]
  unfold perturbedSource perturbationSin
  module

/-- A uniform full-matrix bound; constant2 is sufficient for the lower bound. -/
theorem perturbationRotation_distance (b e : D → ℂ) (h : OrthogonalUnitPair b e) {tau : ℝ} (ht : 0 ≤ tau) :
    ‖(perturbationRotation b e h tau : Matrix D D ℂ) - 1‖ ≤ 2 * tau := by
  have hcoef := perturbation_coefficient_bounds ht
  have hdist := sourcePlaneRotation_distance b e h (perturbationCos tau) (perturbationSin tau)
  rw [abs_of_nonpos (sub_nonpos.mpr hcoef.2.1), abs_of_nonneg hcoef.2.2.1] at hdist
  exact hdist.trans (by linarith [hcoef.2.2.2.1, hcoef.2.2.2.2])

/-- Full perturbed preparation oracle, including every ancillary column. -/
def perturbedPreparation (b e : D → ℂ) (h : OrthogonalUnitPair b e) (tau : ℝ)
    (U : Matrix.unitaryGroup D ℂ) : Matrix.unitaryGroup D ℂ := perturbationRotation b e h tau * U

theorem perturbedPreparation_prepares (b e : D → ℂ) (h : OrthogonalUnitPair b e) (tau : ℝ)
    (U : Matrix.unitaryGroup D ℂ) (i₀ : D) (hU : ∀ i, U i i₀ = b i) :
    ∀ i, perturbedPreparation b e h tau U i i₀ = perturbedSource b e tau i := by
  intro i
  have heq : (perturbedPreparation b e h tau U : Matrix D D ℂ) i i₀ =
      ((perturbationRotation b e h tau : Matrix D D ℂ) *ᵥ b) i := by
    change ((perturbationRotation b e h tau : Matrix D D ℂ) * (U : Matrix D D ℂ)) i i₀ = _
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, hU]
  rw [heq, perturbationRotation_prepares]

theorem perturbedPreparation_distance (b e : D → ℂ) (h : OrthogonalUnitPair b e) {tau : ℝ} (ht : 0 ≤ tau)
    (U : Matrix.unitaryGroup D ℂ) :
    ‖(perturbedPreparation b e h tau U : Matrix D D ℂ) - (U : Matrix D D ℂ)‖ ≤ 2 * tau := by
  have heq : (perturbedPreparation b e h tau U : Matrix D D ℂ) - (U : Matrix D D ℂ) =
      ((perturbationRotation b e h tau : Matrix D D ℂ) - 1) * (U : Matrix D D ℂ) := by
    simp [perturbedPreparation, sub_mul]
  rw [heq]
  exact (Matrix.l2_opNorm_mul _ _).trans ((mul_le_of_le_one_right (norm_nonneg _)
    (QuantumChannelStein.TraceNorm.unitary_opNorm_le_one U)).trans (perturbationRotation_distance b e h ht))

end OptimalQLS.LowerBounds
