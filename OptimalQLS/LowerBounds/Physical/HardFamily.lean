import OptimalQLS.LowerBounds.Physical.Oracles

/-! The concrete hard family on complete binary physical data registers. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds.Physical
open Matrix PhysicalPadding
attribute [local instance] Classical.propDecidable

abbrev paddedDimension (N : ℕ) := physicalDimension (hardOutputDimension N)
abbrev paddedEncoding {N m : ℕ} [NeZero N] {kappa : ℝ} (hk : 4 ≤ kappa) (z : BitString m) :=
  extendEncoding (activeIndex (hardOutputDimension N)) (canonicalHardEncoding hk z)
abbrev paddedPreparation {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) :=
  extendUnitary (activeIndex (hardOutputDimension N)) (canonicalHardPreparation hk he hek hN)
abbrev paddedPerturbedPreparation {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) :=
  extendUnitary (activeIndex (hardOutputDimension N)) (canonicalPerturbedPreparation hk he hek hN)
abbrev paddedPolynomial {N m : ℕ} [NeZero N] {kappa : ℝ} (hk : 4 ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) :=
  extendEncodingPolynomial (activeIndex (hardOutputDimension N)) (canonicalHardPolynomial hk hN)
abbrev paddedSolution (N : ℕ) [NeZero N] {m : ℕ} (kappa estimate : ℝ) (z : BitString m) :=
  insertVector (activeIndex (hardOutputDimension N)) (canonicalSolution N kappa estimate z)
abbrev paddedPairedSolution (N : ℕ) [NeZero N] {m : ℕ} (kappa estimate : ℝ) (z : BitString m) :=
  insertVector (activeIndex (hardOutputDimension N)) (canonicalPairedSolution N kappa estimate z)
abbrev paddedDirection (N : ℕ) :=
  insertVector (activeIndex (hardOutputDimension N)) (canonicalDirection N)
abbrev paddedWeight {N m : ℕ} {kappa : ℝ} (hk : 4 ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) :=
  insertWeight (activeIndex (hardOutputDimension N)) (canonicalWeight hk hN)

theorem paddedPolynomial_eval {N m : ℕ} [NeZero N] [NeZero m] {kappa : ℝ}
    (hk : 4 ≤ kappa) (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    evalMatrix z (paddedPolynomial hk hN) = (paddedEncoding hk z).val :=
  extendEncodingPolynomial_eval _ _ _ z (canonicalHardPolynomial_eval hk hN z)

theorem paddedPolynomial_degree {N m : ℕ} [NeZero N] {kappa : ℝ}
    (hk : 4 ≤ kappa) (hN : N = 2 * historyPadding kappa + 2 * m) :
    MatrixDegreeLE (paddedPolynomial hk hN) 1 :=
  extendEncodingPolynomial_degree _ _ (canonicalHardPolynomial_degree hk hN)

theorem paddedWeight_bound {N m : ℕ} {kappa : ℝ} (hk : 4 ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) : ∀ i, |paddedWeight hk hN i| ≤ 1 :=
  insertWeight_bound _ _ (canonicalWeight_bound hk hN)

theorem padded_signal {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    (5 / 2304 : ℝ) * historyLambda kappa ^ (2 * m) ≤ paritySign z *
      (Matrix.diagonal (fun i => (paddedWeight hk hN i : ℂ)) *
        pureDensity (paddedSolution N kappa estimate z)).trace.re := by
  rw [paddedWeight, insertWeight_diagonal, paddedSolution, insertVector_pureDensity,
    zeroExtend_expectation]
  exact canonical_signal hk he hek hN z

theorem paddedDirection_norm (N : ℕ) : ‖WithLp.toLp 2 (paddedDirection N)‖ = 1 := by
  rw [paddedDirection, insertVector_norm, canonicalDirection_norm]

theorem padded_original_direction_probability {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (z : BitString m) :
    (ketBra (paddedDirection N) (paddedDirection N) *
      pureDensity (paddedSolution N kappa estimate z)).trace.re = 0 := by
  rw [paddedDirection, insertVector_ketBra, paddedSolution, insertVector_pureDensity,
    zeroExtend_expectation]
  exact canonical_original_direction_probability hk z

theorem padded_paired_direction_probability {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    (25 / 61 : ℝ) ≤ (ketBra (paddedDirection N) (paddedDirection N) *
      pureDensity (paddedPairedSolution N kappa estimate z)).trace.re := by
  rw [paddedDirection, insertVector_ketBra, paddedPairedSolution, insertVector_pureDensity,
    zeroExtend_expectation]
  exact canonical_paired_direction_probability hk he hek hN z

theorem padded_preparation_distance {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) :
    ‖(paddedPreparation hk he hek hN).val - (paddedPerturbedPreparation hk he hek hN).val‖ ≤
      5 * estimate / (2 * kappa) := by
  rw [paddedPreparation, paddedPerturbedPreparation, extendUnitary_distance]
  exact canonical_preparation_distance hk he hek hN

theorem paddedSolution_physicalSolution {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    physicalSolution (canonicalHardMatrix N kappa z) (canonicalHardSource N m kappa estimate) =
      WithLp.toLp 2 (paddedSolution N kappa estimate z) := by
  rw [physicalSolution, canonicalSolution_normalizedSolution hk he hek hN z]
  rfl

theorem paddedPairedSolution_physicalSolution {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (z : BitString m) :
    physicalSolution (canonicalHardMatrix N kappa z) (canonicalPerturbedSource N m kappa estimate) =
      WithLp.toLp 2 (paddedPairedSolution N kappa estimate z) := by
  rw [physicalSolution, canonicalPairedSolution_normalizedSolution hk he z]
  rfl

theorem paddedHard_ExactQLSPromise {N m : ℕ} [NeZero N] {kappa estimate eps : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (heps : 0 < eps) (hepsUpper : eps < 1 / 2)
    (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    PhysicalExactQLSPromise (canonicalLowerParameters kappa estimate eps)
      (canonicalHardMatrix N kappa z) (canonicalHardSource N m kappa estimate)
      (paddedEncoding hk z) (paddedPreparation hk he hek hN) :=
  extendExactPromise _ _ _ _ (canonicalHard_ExactQLSPromise hk he hek heps hepsUpper hN z)

theorem paddedPerturbed_ExactQLSPromise {N m : ℕ} [NeZero N] {kappa estimate eps : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (heps : 0 < eps) (hepsUpper : eps < 1 / 2)
    (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    PhysicalExactQLSPromise (canonicalLowerParameters kappa estimate eps)
      (canonicalHardMatrix N kappa z) (canonicalPerturbedSource N m kappa estimate)
      (paddedEncoding hk z) (paddedPerturbedPreparation hk he hek hN) :=
  extendExactPromise _ _ _ _ (canonicalPerturbed_ExactQLSPromise hk he hek heps hepsUpper hN z)

end OptimalQLS.LowerBounds.Physical
