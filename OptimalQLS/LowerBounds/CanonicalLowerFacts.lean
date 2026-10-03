import OptimalQLS.LowerBounds.CanonicalPromises
import OptimalQLS.LowerBounds.HardFamilyDecoder

/-! Polynomial and distinguishing-observable facts after conventional rewiring. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix

def canonicalHardPolynomial {N m : ℕ} [NeZero N] {kappa : ℝ} (hk : 4 ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) :
    Matrix (OptimalQLS.SignalIndex 1 × Fin (hardOutputDimension N))
      (OptimalQLS.SignalIndex 1 × Fin (hardOutputDimension N)) (InputPolynomial m) :=
  (hardFamilyPolynomial hk hN).submatrix (canonicalSignalCoordinates N) (canonicalSignalCoordinates N)

theorem canonicalHardPolynomial_eval {N m : ℕ} [NeZero N] [NeZero m] {kappa : ℝ} (hk : 4 ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    evalMatrix z (canonicalHardPolynomial hk hN) = canonicalHardEncoding (N := N) hk z := by
  rw [canonicalHardPolynomial, evalMatrix_submatrix, hardFamilyPolynomial_eval hk hN]
  rfl

theorem canonicalHardPolynomial_degree {N m : ℕ} [NeZero N] {kappa : ℝ} (hk : 4 ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) : MatrixDegreeLE (canonicalHardPolynomial hk hN) 1 :=
  matrixDegree_submatrix (hardFamilyPolynomial_degree hk hN) _ _

def canonicalWeight {N m : ℕ} {kappa : ℝ} (hk : 4 ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) : Fin (hardOutputDimension N) → ℝ :=
  hardBasisWeight hk hN ∘ canonicalDataCoordinates N

theorem canonicalWeight_bound {N m : ℕ} {kappa : ℝ} (hk : 4 ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) : ∀ i, |canonicalWeight hk hN i| ≤ 1 :=
  fun _ => hardBasisWeight_bound hk hN _

theorem canonical_diagonal {N m : ℕ} {kappa : ℝ} (hk : 4 ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) :
    Matrix.diagonal (fun i => (canonicalWeight hk hN i : ℂ)) =
      (hardFamilyObservable hk hN).submatrix (canonicalDataCoordinates N) (canonicalDataCoordinates N) := by
  rw [hardFamilyObservable_diagonal, Matrix.submatrix_diagonal_equiv]
  rfl

theorem canonical_signal {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    (5 / 2304 : ℝ) * historyLambda kappa ^ (2 * m) ≤ paritySign z *
      (Matrix.diagonal (fun i => (canonicalWeight hk hN i : ℂ)) * pureDensity (canonicalSolution N kappa estimate z)).trace.re := by
  rw [canonical_diagonal, canonicalSolution, pureDensity_reindex, expectation_reindex]
  exact hardFamily_density_signal hk he hek hN z

def canonicalDirection (N : ℕ) : Fin (hardOutputDimension N) → ℂ :=
  (dilatedLastDirection (D := HistoryBasis N)) ∘ canonicalDataCoordinates N

theorem canonicalDirection_norm (N : ℕ) : ‖WithLp.toLp 2 (canonicalDirection N)‖ = 1 := by
  rw [canonicalDirection, euclidean_norm_comp_equiv]
  exact dilatedLastDirection_norm

theorem canonical_original_direction_probability {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (z : BitString m) :
    (ketBra (canonicalDirection N) (canonicalDirection N) * pureDensity (canonicalSolution N kappa estimate z)).trace.re = 0 := by
  have hp : ketBra (canonicalDirection N) (canonicalDirection N) =
      (ketBra (dilatedLastDirection (D := HistoryBasis N)) dilatedLastDirection).submatrix (canonicalDataCoordinates N) (canonicalDataCoordinates N) := by ext i j; rfl
  rw [hp, canonicalSolution, pureDensity_reindex, expectation_reindex]
  exact hardFamily_original_direction_probability hk z

theorem canonical_paired_direction_probability {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    (25 / 61 : ℝ) ≤ (ketBra (canonicalDirection N) (canonicalDirection N) * pureDensity (canonicalPairedSolution N kappa estimate z)).trace.re := by
  have hp : ketBra (canonicalDirection N) (canonicalDirection N) =
      (ketBra (dilatedLastDirection (D := HistoryBasis N)) dilatedLastDirection).submatrix (canonicalDataCoordinates N) (canonicalDataCoordinates N) := by ext i j; rfl
  rw [hp, canonicalPairedSolution, pureDensity_reindex, expectation_reindex]
  exact hardFamily_paired_direction_probability hk he hek hN z

theorem canonical_preparation_distance {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) :
    ‖(canonicalHardPreparation hk he hek hN : Matrix (Fin (hardOutputDimension N)) (Fin (hardOutputDimension N)) ℂ) -
      (canonicalPerturbedPreparation hk he hek hN : Matrix (Fin (hardOutputDimension N)) (Fin (hardOutputDimension N)) ℂ)‖ ≤
      5 * estimate / (2 * kappa) := by
  have heq : (canonicalHardPreparation hk he hek hN : Matrix (Fin (hardOutputDimension N)) (Fin (hardOutputDimension N)) ℂ) -
      (canonicalPerturbedPreparation hk he hek hN : Matrix (Fin (hardOutputDimension N)) (Fin (hardOutputDimension N)) ℂ) =
      ((hardFamilyPreparation hk he hek hN : Matrix (HardFamilyIndex N) (HardFamilyIndex N) ℂ) -
        (hardFamilyPerturbedPreparation hk he hek hN : Matrix (HardFamilyIndex N) (HardFamilyIndex N) ℂ)).submatrix
        (canonicalDataCoordinates N) (canonicalDataCoordinates N) := rfl
  rw [heq, matrix_norm_reindex, norm_sub_rev]
  exact hardFamilyPerturbedPreparation_distance hk he hek hN

end OptimalQLS.LowerBounds
