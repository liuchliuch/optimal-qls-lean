import OptimalQLS.LowerBounds.ParityHistoryFamily
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# A fixed Hermitian parity observable on the actual normalized history state

The observable is diagonal Pauli Z on the tail clock interval and zero
elsewhere. It is independent of z and has Euclidean operator norm at most1.
The pure-state quadratic expectation equals the parity sign times the literal
Born probability already bounded in the history construction.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix

def boolSign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem boolSign_xor (a b : Bool) :
    boolSign (Bool.xor a b) = boolSign a * boolSign b := by cases a <;> cases b <;> norm_num [boolSign]

@[simp] theorem boolSign_sq (b : Bool) : boolSign b ^ 2 = 1 := by cases b <;> norm_num [boolSign]

theorem boolSign_xorFold (l : List Bool) : boolSign (xorFold l) = (l.map boolSign).prod := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [xorFold, ih]

theorem boolSign_xorFold_ofFn {m : ℕ} (z : BitString m) :
    boolSign (xorFold (List.ofFn z)) = paritySign z := by
  rw [boolSign_xorFold]
  simp [paritySign, boolSign, List.map_ofFn, List.prod_ofFn]

def tailClockSet {N ell m : ℕ} (hell : 0 < ell) (hN : 2 * ell + m ≤ N) : Finset (Fin N) :=
  Finset.univ.image (tailClock hell hN)

/-- The fixed observable M of the history system before norm adjustment. -/
def historyObservable {N ell m : ℕ} (hell : 0 < ell) (hN : 2 * ell + m ≤ N) :
    Matrix (HistoryBasis N) (HistoryBasis N) ℂ :=
  Matrix.diagonal (fun b => if b.1 ∈ tailClockSet hell hN then (boolSign b.2 : ℂ) else 0)

theorem historyObservable_hermitian {N ell m : ℕ} (hell : 0 < ell) (hN : 2 * ell + m ≤ N) :
    (historyObservable hell hN).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro b
  split_ifs <;> simp [isSelfAdjoint_iff]

theorem historyObservable_norm_le_one {N ell m : ℕ} (hell : 0 < ell)
    (hN : 2 * ell + m ≤ N) : ‖historyObservable hell hN‖ ≤ 1 := by
  rw [historyObservable, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  rintro ⟨j, b⟩
  split_ifs <;> cases b <;> norm_num [boolSign]

/-- Actual pure-state quadratic expectation, with the standard complex inner product. -/
def pureExpectation {n : Type*} [Fintype n] (M : Matrix n n ℂ) (v : n → ℂ) : ℝ :=
  (∑ i, star (v i) * (M *ᵥ v) i).re

theorem pureExpectation_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (d : n → ℝ) (v : n → ℂ) :
    pureExpectation (Matrix.diagonal (fun i => (d i : ℂ))) v = ∑ i, d i * ‖v i‖ ^ 2 := by
  simp only [pureExpectation, Matrix.mulVec_diagonal, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h : star (v i) * ((d i : ℂ) * v i) = (d i * ‖v i‖ ^ 2 : ℝ) := by
    rw [Complex.ofReal_mul, Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    change star (v i) * ((d i : ℂ) * v i) = (d i : ℂ) * (star (v i) * v i)
    ring
  exact congrArg Complex.re h

/-- The diagonal expectation is the signed work measurement summed over the
same injective clock outcomes as `historyTailProbability`. -/
theorem historyObservable_expectation {N ell m : ℕ} (hell : 0 < ell)
    (hN : 2 * ell + m ≤ N) (v : HistoryBasis N → ℂ) :
    pureExpectation (historyObservable hell hN) v =
      ∑ k : Fin ell, ∑ b : Bool, boolSign b * ‖v (tailClock hell hN k, b)‖ ^ 2 := by
  have hmatrix : historyObservable hell hN = Matrix.diagonal
      (fun b : HistoryBasis N => ((if b.1 ∈ tailClockSet hell hN then boolSign b.2 else 0 : ℝ) : ℂ)) := by
    ext i j
    simp [historyObservable, apply_ite]
  rw [hmatrix, pureExpectation_diagonal, Fintype.sum_prod_type]
  simp only [ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [← Finset.sum_filter]
  have hfilter : Finset.univ.filter (fun j : Fin N => j ∈ tailClockSet hell hN) = tailClockSet hell hN := by
    ext j; simp
  rw [hfilter, tailClockSet, Finset.sum_image]
  intro i hi j hj heq
  exact tailClock_injective hell hN heq

lemma signed_work_expectation (v : Bool → ℂ) (p : Bool) (hzero : ∀ b, b ≠ p → v b = 0) :
    (∑ b : Bool, boolSign b * ‖v b‖ ^ 2) = boolSign p * ∑ b : Bool, ‖v b‖ ^ 2 := by
  cases p <;> simp [Fintype.sum_bool, boolSign, hzero]

/-- Exact expectation identity on each literal parity-history state. -/
theorem parity_history_observable_expectation {N m : ℕ} [NeZero N] {kappa : ℝ}
    (hk : 4 ≤ kappa) (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    pureExpectation
      (historyObservable (historyPadding_pos hk) (show 2 * historyPadding kappa + m ≤ N by omega))
      (normalizedHistorySolution (fixedParityProfile (N := N) (historyPadding kappa) z)
        (historyPadding kappa) (historyLambda kappa)) =
      paritySign z * historyTailProbability
        (fixedParityProfile (N := N) (historyPadding kappa) z) (historyPadding_pos hk)
        (show 2 * historyPadding kappa + m ≤ N by omega) (historyLambda kappa) := by
  rw [historyObservable_expectation, ← boolSign_xorFold_ofFn z]
  unfold historyTailProbability
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply signed_work_expectation
  intro b hb
  have hb' : b = !(xorFold (List.ofFn z)) := by
    cases b <;> cases hp : xorFold (List.ofFn z) <;> simp_all
  rw [hb']
  exact parity_history_tail_work_bit hk hN z k

/-- The paper's parity signal before the norm-adjusting direct sum. -/
theorem parity_history_observable_signal {N m : ℕ} [NeZero N] {kappa : ℝ}
    (hk : 4 ≤ kappa) (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    historyLambda kappa ^ (2 * m) / 256 ≤ paritySign z *
      pureExpectation
        (historyObservable (historyPadding_pos hk) (show 2 * historyPadding kappa + m ≤ N by omega))
        (normalizedHistorySolution (fixedParityProfile (N := N) (historyPadding kappa) z)
          (historyPadding kappa) (historyLambda kappa)) := by
  rw [parity_history_observable_expectation hk hN z, ← mul_assoc,
    ← boolSign_xorFold_ofFn z, ← pow_two, boolSign_sq, one_mul]
  exact parity_history_tail_probability hk hN z

end OptimalQLS.LowerBounds
