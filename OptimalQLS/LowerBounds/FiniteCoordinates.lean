import OptimalQLS.LowerBounds.PairedNormalization
import OptimalQLS.LowerBounds.QueryPortDistance

/-! Exact transport of the hard family to the finite output coordinates of a program. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
variable {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

theorem matrix_norm_reindex (M : Matrix D D ℂ) (e : E ≃ D) : ‖M.submatrix e e‖ = ‖M‖ := by
  apply le_antisymm (matrix_norm_submatrix_equiv_le M e)
  have h := matrix_norm_submatrix_equiv_le (M.submatrix e e) e.symm
  simpa [Matrix.submatrix_submatrix] using h

theorem matrix_trace_reindex (M : Matrix D D ℂ) (e : E ≃ D) : (M.submatrix e e).trace = M.trace :=
  Equiv.sum_comp e (fun i => M i i)

theorem pureDensity_reindex (u : D → ℂ) (e : E ≃ D) : pureDensity (u ∘ e) = (pureDensity u).submatrix e e := by
  ext i j
  rfl

theorem expectation_reindex (M X : Matrix D D ℂ) (e : E ≃ D) :
    ((M.submatrix e e) * (X.submatrix e e)).trace = (M * X).trace := by
  rw [Matrix.submatrix_mul_equiv]
  exact matrix_trace_reindex _ e

def hardOutputDimension (N : ℕ) : ℕ := Fintype.card (HardFamilyIndex N)

def hardOutputCoordinates (N : ℕ) : Fin (hardOutputDimension N) ≃ HardFamilyIndex N :=
  (Fintype.equivFin (HardFamilyIndex N)).symm

def hardOutputSolution (N : ℕ) [NeZero N] {m : ℕ} (kappa estimate : ℝ) (z : BitString m) :
    Fin (hardOutputDimension N) → ℂ := normalizedHardFamilySolution N kappa estimate z ∘ hardOutputCoordinates N

def hardOutputPairedSolution (N : ℕ) [NeZero N] {m : ℕ} (kappa estimate : ℝ) (z : BitString m) :
    Fin (hardOutputDimension N) → ℂ := hardFamilyPairedSolution N kappa estimate z ∘ hardOutputCoordinates N

def hardOutputDirection (N : ℕ) : Fin (hardOutputDimension N) → ℂ :=
  (dilatedLastDirection (D := HistoryBasis N)) ∘ hardOutputCoordinates N

theorem hardOutputDirection_norm (N : ℕ) : ‖WithLp.toLp 2 (hardOutputDirection N)‖ = 1 := by
  rw [hardOutputDirection, euclidean_norm_comp_equiv]
  exact dilatedLastDirection_norm

theorem hardOutput_original_direction_probability {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (z : BitString m) :
    (ketBra (hardOutputDirection N) (hardOutputDirection N) * pureDensity (hardOutputSolution N kappa estimate z)).trace.re = 0 := by
  have hp : ketBra (hardOutputDirection N) (hardOutputDirection N) =
      (ketBra (dilatedLastDirection (D := HistoryBasis N)) dilatedLastDirection).submatrix (hardOutputCoordinates N) (hardOutputCoordinates N) := by
    ext i j
    rfl
  rw [hp, hardOutputSolution, pureDensity_reindex, expectation_reindex]
  exact hardFamily_original_direction_probability hk z

theorem hardOutput_paired_direction_probability {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    (25 / 61 : ℝ) ≤ (ketBra (hardOutputDirection N) (hardOutputDirection N) * pureDensity (hardOutputPairedSolution N kappa estimate z)).trace.re := by
  have hp : ketBra (hardOutputDirection N) (hardOutputDirection N) =
      (ketBra (dilatedLastDirection (D := HistoryBasis N)) dilatedLastDirection).submatrix (hardOutputCoordinates N) (hardOutputCoordinates N) := by
    ext i j
    rfl
  rw [hp, hardOutputPairedSolution, pureDensity_reindex, expectation_reindex]
  exact hardFamily_paired_direction_probability hk he hek hN z

end OptimalQLS.LowerBounds
