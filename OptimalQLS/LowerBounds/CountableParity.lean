import OptimalQLS.LowerBounds.ReachableBranches
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Unbounded-time parity lower bound for countable concrete terminal branches

Every branch is still an explicit finite matrix/bit-query path, but there may
be countably many terminal branches with different finite workspace sizes and
unbounded running times. Born mass is subprobability mass: every finite partial
sum is at most1. This legitimate probabilistic condition proves summability;
no infinite polynomial, assumed degree bound, or hardness certificate occurs.

The theorem concerns this operational terminal-branch representation. A fully
general programming-language semantics still needs a theorem enumerating its
finite terminating branches in this form. Nontermination contributes no
terminal output, and success is represented by the actual signed terminal
Born-weight sum.
-/
noncomputable section
open scoped BigOperators
namespace OptimalQLS.LowerBounds
open MvPolynomial

/-- The full parity coefficient of a genuinely executed short branch vanishes. -/
theorem short_path_parity_sum_zero {m w : ℕ} (path : QueryPath m w) (weight : ℝ)
    (hshort : 2 * path.queries < m) :
    (∑ z : BitString m, paritySign z * (weight * path.bornWeight z)) = 0 := by
  let p : MvPolynomial (Fin m) ℂ := C (weight : ℂ) * path.weightPolynomial
  have hd : p.totalDegree < m := by
    apply lt_of_le_of_lt _ hshort
    apply (totalDegree_mul _ _).trans
    simpa using path.weight_totalDegree
  have hz := parityCoefficient_eq_zero_of_degree_lt p hd
  have heval (z : BitString m) : eval (bitValue z) p = (weight * path.bornWeight z : ℝ) := by
    simp [p]
  simp only [parityCoefficient, heval, ← Complex.ofReal_mul, ← Complex.ofReal_sum] at hz
  exact_mod_cast hz

/-- Actual possibly countably infinite signed terminal-output bias. -/
def countableBranchBias {m : ℕ} {ι : Type*} (w : ι → ℕ)
    (paths : ∀ k, QueryPath m (w k)) (weights : ι → ℝ) (z : BitString m) : ℝ :=
  ∑' k, weights k * (paths k).bornWeight z

/-- Bounded actual Born partial sums imply summability of signed branch weights. -/
theorem signed_branch_summable {m : ℕ} {ι : Type*} (w : ι → ℕ)
    (paths : ∀ k, QueryPath m (w k)) (weights : ι → ℝ)
    (hweights : ∀ k, |weights k| ≤ 1) (z : BitString m)
    (hmass : ∀ s : Finset ι, ∑ k ∈ s, (paths k).bornWeight z ≤ 1) :
    Summable (fun k => weights k * (paths k).bornWeight z) := by
  have hs : Summable (fun k => (paths k).bornWeight z) :=
    summable_of_sum_le (fun k => (paths k).bornWeight_nonneg z) hmass
  apply hs.of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ((paths k).bornWeight_nonneg z)]
  exact mul_le_of_le_one_left ((paths k).bornWeight_nonneg z) (hweights k)

/-- Countable operational unbounded-error parity lower bound. There is an
actual positive-probability terminal run using at least m/2 queries, even if
there are infinitely many possible stopping times and branch-dependent finite
workspaces. Finite partial Born mass≤1 is the only summability input. -/
theorem countable_branch_parity_hard_run {m : ℕ} {ι : Type*} [Countable ι]
    (w : ι → ℕ) (paths : ∀ k, QueryPath m (w k)) (weights : ι → ℝ)
    (hweights : ∀ k, |weights k| ≤ 1)
    (hmass : ∀ (z : BitString m) (s : Finset ι), ∑ k ∈ s, (paths k).bornWeight z ≤ 1)
    (hsuccess : ∀ z : BitString m,
      0 < paritySign z * countableBranchBias w paths weights z) :
    ∃ (z : BitString m) (k : ι),
      0 < (paths k).bornWeight z ∧ m ≤ 2 * (paths k).queries := by
  classical
  by_contra hno
  push_neg at hno
  have hbranch : ∀ k : ι,
      (∑ z : BitString m, paritySign z * (weights k * (paths k).bornWeight z)) = 0 := by
    intro k
    by_cases hshort : 2 * (paths k).queries < m
    · exact short_path_parity_sum_zero (paths k) (weights k) hshort
    · have hlong : m ≤ 2 * (paths k).queries := by omega
      apply Finset.sum_eq_zero
      intro z _
      have hz : (paths k).bornWeight z = 0 := by
        apply le_antisymm _ ((paths k).bornWeight_nonneg z)
        exact le_of_not_gt (fun hp => (not_le.mpr (hno z k hp)) hlong)
      simp [hz]
  have hsum (z : BitString m) : Summable (fun k => weights k * (paths k).bornWeight z) :=
    signed_branch_summable w paths weights hweights z (hmass z)
  have hzero : (∑ z : BitString m, paritySign z * countableBranchBias w paths weights z) = 0 := by
    calc
      _ = ∑ z : BitString m, ∑' k, paritySign z * (weights k * (paths k).bornWeight z) := by
        apply Finset.sum_congr rfl
        intro z _
        exact ((hsum z).tsum_mul_left (paritySign z)).symm
      _ = ∑' k, ∑ z : BitString m, paritySign z * (weights k * (paths k).bornWeight z) :=
        (Summable.tsum_finsetSum (fun z _ => (hsum z).mul_left (paritySign z))).symm
      _ = 0 := by simp [hbranch]
  have hpositive : 0 < ∑ z : BitString m, paritySign z * countableBranchBias w paths weights z :=
    Finset.sum_pos (fun z _ => hsuccess z) Finset.univ_nonempty
  rw [hzero] at hpositive
  exact lt_irrefl 0 hpositive

end OptimalQLS.LowerBounds
