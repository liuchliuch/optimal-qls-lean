import OptimalQLS.Reduction.Normalized
import OptimalQLS.LowerBounds.PureDensity
import OptimalQLS.LowerBounds.VariableBorn

/-! Measuring the literal added data qubit. The squared probability estimate
uses the whole unit vector, including its rejected component. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.Reduction
open Matrix LowerBounds
variable {D : Type*} [Fintype D] [DecidableEq D]

def leftPart (y : EuclideanSpace ℂ (D ⊕ D)) : EuclideanSpace ℂ D :=
  WithLp.toLp 2 (fun i => y (.inl i))

def rightPart (y : EuclideanSpace ℂ (D ⊕ D)) : EuclideanSpace ℂ D :=
  WithLp.toLp 2 (fun i => y (.inr i))

theorem parts_norm_sq (y : EuclideanSpace ℂ (D ⊕ D)) :
    ‖y‖^2 = ‖leftPart y‖^2 + ‖rightPart y‖^2 := by
  simpa [leftPart, rightPart, EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]

theorem parts_error_sq (y : EuclideanSpace ℂ (D ⊕ D)) (x : EuclideanSpace ℂ D) :
    ‖y - WithLp.toLp 2 (rightState (fun i => x i))‖^2 =
      ‖leftPart y‖^2 + ‖rightPart y - x‖^2 := by
  simpa [leftPart, rightPart, rightState, EuclideanSpace.norm_sq_eq,
    Fintype.sum_sum_type]

theorem normalize_error_two (v x : EuclideanSpace ℂ D) (hv : v ≠ 0) (hx : ‖x‖ = 1) :
    ‖NormedSpace.normalize v - x‖ ≤ 2 * ‖v - x‖ := by
  have hnv := NormedSpace.norm_normalize hv
  have he : NormedSpace.normalize v - v = (1 - ‖v‖) • NormedSpace.normalize v := by
    rw [sub_smul, one_smul, NormedSpace.norm_smul_normalize]
  have hn : ‖NormedSpace.normalize v - v‖ ≤ ‖v - x‖ := by
    rw [he, norm_smul, hnv, mul_one, Real.norm_eq_abs, abs_sub_comm]
    simpa [hx] using abs_norm_sub_norm_le v x
  calc
    ‖NormedSpace.normalize v - x‖ ≤ ‖NormedSpace.normalize v - v‖ + ‖v - x‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * ‖v - x‖ := by linarith

/-- A complete extraction guarantee, with the Born probability of the actual
right-coordinate measurement. The epsilon convention is that of Problem 2.2. -/
theorem extraction_guarantee (y : EuclideanSpace ℂ (D ⊕ D))
    (x : EuclideanSpace ℂ D) {ε : ℝ} (hy : ‖y‖ = 1) (hx : ‖x‖ = 1)
    (hε0 : 0 < ε) (hε1 : ε < 1/2)
    (herr : ‖y - WithLp.toLp 2 (rightState (fun i => x i))‖ ≤ ε/2) :
    ‖rightPart y - x‖ ≤ ε/2 ∧
    3/4 ≤ ‖rightPart y‖ ∧
    1 - ε^2/4 ≤ ‖rightPart y‖^2 ∧
    9/16 ≤ ‖rightPart y‖^2 ∧
    ‖NormedSpace.normalize (rightPart y) - x‖ ≤ ε ∧
    ‖NormedSpace.normalize (rightPart y)‖ = 1 := by
  have hsq := pow_le_pow_left₀ (norm_nonneg _) herr 2
  rw [parts_error_sq] at hsq
  have hr : ‖rightPart y - x‖ ≤ ε/2 := by
    nlinarith [sq_nonneg ‖leftPart y‖, norm_nonneg (rightPart y - x)]
  have hn : 3/4 ≤ ‖rightPart y‖ := by
    have h := norm_sub_norm_le x (rightPart y)
    rw [hx, norm_sub_rev] at h
    linarith
  have hp : 1 - ε^2/4 ≤ ‖rightPart y‖^2 := by
    have ht := parts_norm_sq y
    rw [hy] at ht
    nlinarith [sq_nonneg ‖rightPart y - x‖]
  have hn0 : rightPart y ≠ 0 := by
    intro h; rw [h, norm_zero] at hn; norm_num at hn
  refine ⟨hr,hn,hp,?_,?_,NormedSpace.norm_normalize hn0⟩
  · nlinarith
  · exact (normalize_error_two _ x hn0 hx).trans (by linarith)

/-- Literal rectangular Kraus operator for outcome one of the data qubit. -/
def extractOne : Matrix D (D ⊕ D) ℂ := fun i j =>
  match j with | .inl _ => 0 | .inr k => if i = k then 1 else 0

theorem extractOne_mulVec (y : D ⊕ D → ℂ) :
    extractOne *ᵥ y = fun i => y (.inr i) := by
  ext i
  simp [extractOne, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

theorem extractOne_bornMass (y : EuclideanSpace ℂ (D ⊕ D)) :
    bornMass (extractOne *ᵥ (fun i => y i)) = ‖rightPart y‖^2 := by
  rw [extractOne_mulVec, bornMass_eq_norm_sq]
  rfl

end OptimalQLS.Reduction
