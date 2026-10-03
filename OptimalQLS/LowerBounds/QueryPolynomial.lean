import OptimalQLS.LowerBounds.Parity
import Mathlib.Data.Matrix.Mul

/-!
# Concrete bit-query paths and their amplitude polynomials

A path is an actual complex state vector subjected to input-independent
matrix operations and the ordinary reversible bit oracle. Matrix operations
need not be unitary: unnormalized post-measurement vectors and fixed Kraus
branches are included. Branch probabilities below are literal Born weights.
There is no polynomial-degree certificate in the model; the degree bound is
proved from the operational recursion.
-/
noncomputable section
open scoped BigOperators
namespace OptimalQLS.LowerBounds
open MvPolynomial

/-- An optional query index implements a controlled query; `none` is idle. -/
abbrev QueryBasis (m w : ℕ) := Option (Fin m) × Bool × Fin w

/-- The standard bit oracle, including an idle control sector. -/
def queryBasisMap {m w : ℕ} (z : BitString m) (b : QueryBasis m w) : QueryBasis m w :=
  match b.1 with
  | none => b
  | some i => (some i, Bool.xor b.2.1 (z i), b.2.2)

@[simp] theorem queryBasisMap_involutive {m w : ℕ} (z : BitString m) :
    Function.Involutive (queryBasisMap (w := w) z) := by
  intro b
  rcases b with ⟨i, c, k⟩
  cases i with
  | none => rfl
  | some i => cases c <;> cases hz : z i <;> simp [queryBasisMap, hz]

def bitOraclePermutation {m w : ℕ} (z : BitString m) : QueryBasis m w ≃ QueryBasis m w :=
  (queryBasisMap_involutive z).toPerm

/-- State-vector action of the reversible bit oracle. Since it is involutive,
its input and output coordinate permutations coincide. -/
def applyBitOracle {m w : ℕ} (z : BitString m) (ψ : QueryBasis m w → ℂ) :
    QueryBasis m w → ℂ := fun b => ψ (queryBasisMap z b)

/-- Finite operational path; gates can also be Kraus operators of a fixed
measurement branch. All coefficients are independent of the hidden input. -/
inductive QueryPath (m w : ℕ) where
  | initial (ψ : QueryBasis m w → ℂ)
  | gate (U : Matrix (QueryBasis m w) (QueryBasis m w) ℂ) (prev : QueryPath m w)
  | query (prev : QueryPath m w)

def QueryPath.queries {m w : ℕ} : QueryPath m w → ℕ
  | .initial _ => 0
  | .gate _ prev => prev.queries
  | .query prev => prev.queries + 1

def QueryPath.state {m w : ℕ} (z : BitString m) : QueryPath m w → QueryBasis m w → ℂ
  | .initial ψ => ψ
  | .gate U prev => fun b => ∑ c, U b c * prev.state z c
  | .query prev => applyBitOracle z (prev.state z)

def QueryPath.amplitudePolynomial {m w : ℕ} :
    QueryPath m w → QueryBasis m w → MvPolynomial (Fin m) ℂ
  | .initial ψ => fun b => C (ψ b)
  | .gate U prev => fun b => ∑ c, C (U b c) * prev.amplitudePolynomial c
  | .query prev => fun b => match b.1 with
      | none => prev.amplitudePolynomial b
      | some i =>
        (1 - X i) * prev.amplitudePolynomial b +
        X i * prev.amplitudePolynomial (some i, !b.2.1, b.2.2)

/-- Exact agreement between polynomial evaluation and operational amplitudes. -/
theorem QueryPath.eval_amplitudePolynomial {m w : ℕ} (path : QueryPath m w)
    (z : BitString m) (b : QueryBasis m w) :
    eval (bitValue z) (path.amplitudePolynomial b) = path.state z b := by
  induction path generalizing b with
  | initial ψ => simp [amplitudePolynomial, state]
  | gate U prev ih => simp [amplitudePolynomial, state, ih]
  | query prev ih =>
    rcases b with ⟨i, c, k⟩
    cases i with
    | none => exact ih _
    | some i =>
      cases hz : z i <;> cases c <;>
        simp [amplitudePolynomial, state, applyBitOracle, queryBasisMap, bitValue, hz, ih]

/-- Each actual oracle call increases amplitude total degree by at most one. -/
theorem QueryPath.amplitude_totalDegree {m w : ℕ} (path : QueryPath m w)
    (b : QueryBasis m w) :
    (path.amplitudePolynomial b).totalDegree ≤ path.queries := by
  induction path generalizing b with
  | initial ψ => simp [amplitudePolynomial, queries]
  | gate U prev ih =>
    apply totalDegree_finsetSum_le
    intro c _
    exact (totalDegree_mul _ _).trans (by simpa using ih c)
  | query prev ih =>
    rcases b with ⟨i, c, k⟩
    cases i with
    | none => exact (ih _).trans (Nat.le_succ _)
    | some i =>
      change ((_ * _ + _ * _ : MvPolynomial (Fin m) ℂ).totalDegree) ≤ _
      apply (totalDegree_add _ _).trans
      apply max_le
      · apply (totalDegree_mul _ _).trans
        have h1 : (1 - X i : MvPolynomial (Fin m) ℂ).totalDegree ≤ 1 :=
          (totalDegree_sub _ _).trans (by simp)
        have h2 := ih (some i, c, k)
        change _ ≤ prev.queries + 1
        omega
      · apply (totalDegree_mul _ _).trans
        have h2 := ih (some i, !c, k)
        simp only [totalDegree_X]
        change 1 + _ ≤ prev.queries + 1
        omega

/-- Conjugating polynomial coefficients preserves a degree upper bound. -/
theorem totalDegree_conjugate_le {m : ℕ} (p : MvPolynomial (Fin m) ℂ) :
    (map (starRingEnd ℂ) p).totalDegree ≤ p.totalDegree := by
  exact Finset.sup_mono (support_map_subset _ _)

@[simp] theorem eval_conjugate {m : ℕ} (p : MvPolynomial (Fin m) ℂ)
    (z : BitString m) :
    eval (bitValue z) (map (starRingEnd ℂ) p) = star (eval (bitValue z) p) := by
  rw [eval_map]
  change _ = (starRingEnd ℂ) (eval (bitValue z) p)
  rw [eval₂_comp]
  congr 1
  funext i
  simp [Function.comp_def, bitValue]

/-- Actual squared norm, with no normalization or success promise imposed. -/
def QueryPath.bornWeight {m w : ℕ} (path : QueryPath m w) (z : BitString m) : ℝ :=
  ∑ b, Complex.normSq (path.state z b)

theorem QueryPath.bornWeight_nonneg {m w : ℕ} (path : QueryPath m w) (z : BitString m) :
    0 ≤ path.bornWeight z :=
  Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

def QueryPath.weightPolynomial {m w : ℕ} (path : QueryPath m w) :
    MvPolynomial (Fin m) ℂ :=
  ∑ b, path.amplitudePolynomial b * map (starRingEnd ℂ) (path.amplitudePolynomial b)

@[simp] theorem QueryPath.eval_weightPolynomial {m w : ℕ} (path : QueryPath m w)
    (z : BitString m) :
    eval (bitValue z) path.weightPolynomial = (path.bornWeight z : ℂ) := by
  simp only [weightPolynomial, map_sum, map_mul, eval_conjugate, eval_amplitudePolynomial]
  simp [bornWeight, Complex.mul_conj]

theorem QueryPath.weight_totalDegree {m w : ℕ} (path : QueryPath m w) :
    path.weightPolynomial.totalDegree ≤ 2 * path.queries := by
  apply totalDegree_finsetSum_le
  intro b _
  apply (totalDegree_mul _ _).trans
  have h1 := path.amplitude_totalDegree b
  have h2 := totalDegree_conjugate_le (path.amplitudePolynomial b)
  omega

/-- Bias from finitely many concrete unnormalized terminal branches. With
weights `+1` and `-1` this is probability(output 0) minus probability(output 1).
Weight zero is permitted for discarded or fair-random failure branches. -/
def branchBias {m w : ℕ} {ι : Type*} [Fintype ι] (paths : ι → QueryPath m w) (weights : ι → ℝ)
    (z : BitString m) : ℝ :=
  ∑ k, weights k * (paths k).bornWeight z

def branchBiasPolynomial {m w : ℕ} {ι : Type*} [Fintype ι] (paths : ι → QueryPath m w)
    (weights : ι → ℝ) : MvPolynomial (Fin m) ℂ :=
  ∑ k, C (weights k : ℂ) * (paths k).weightPolynomial

@[simp] theorem eval_branchBiasPolynomial {m w : ℕ} {ι : Type*} [Fintype ι]
    (paths : ι → QueryPath m w) (weights : ι → ℝ) (z : BitString m) :
    eval (bitValue z) (branchBiasPolynomial paths weights) = (branchBias paths weights z : ℂ) := by
  simp [branchBiasPolynomial, branchBias]

theorem branchBiasPolynomial_totalDegree {m w T : ℕ} {ι : Type*} [Fintype ι]
    (paths : ι → QueryPath m w) (weights : ι → ℝ)
    (hqueries : ∀ k, (paths k).queries ≤ T) :
    (branchBiasPolynomial paths weights).totalDegree ≤ 2 * T := by
  apply totalDegree_finsetSum_le
  intro k _
  apply (totalDegree_mul _ _).trans
  have h := (paths k).weight_totalDegree
  simp only [totalDegree_C, zero_add]
  exact h.trans (Nat.mul_le_mul_left _ (hqueries k))

/-- Operational unbounded-error parity lower bound for any finite family of
Kraus/matrix branch paths with at most `T` explicit bit queries on each path.
This includes fixed-query unitary circuits and finite adaptive instruments
once their terminal unnormalized branches are enumerated. -/
theorem finite_branch_parity_lower_bound {m w T : ℕ} {ι : Type*} [Fintype ι]
    (paths : ι → QueryPath m w) (weights : ι → ℝ)
    (hqueries : ∀ k, (paths k).queries ≤ T)
    (hsuccess : ∀ z : BitString m, 0 < paritySign z * branchBias paths weights z) :
    m ≤ 2 * T := by
  have hsign : ∀ z : BitString m,
      0 < paritySign z * (eval (bitValue z) (branchBiasPolynomial paths weights)).re := by
    simpa using hsuccess
  exact (degree_ge_of_strict_parity_sign _ hsign).trans
    (branchBiasPolynomial_totalDegree paths weights hqueries)

end OptimalQLS.LowerBounds
