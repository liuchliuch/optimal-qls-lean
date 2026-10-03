import OptimalQLS.LowerBounds.QueryPolynomial

/-!
# Lower bounds count genuinely reachable runs

A terminal Kraus path with zero Born weight on every input must not count as
a run in the worst-case query convention. This module removes all paths above
a proposed bound and proves that the resulting polynomial still equals the
actual bias whenever such paths are unreachable. Thus the parity lower bound
selects a positive-probability run, not a dead syntactic branch.
-/
noncomputable section
open scoped BigOperators
namespace OptimalQLS.LowerBounds
open MvPolynomial

def cutoffBiasPolynomial {m w : ℕ} {ι : Type*} [Fintype ι] (paths : ι → QueryPath m w)
    (weights : ι → ℝ) (T : ℕ) : MvPolynomial (Fin m) ℂ :=
  ∑ k, if (paths k).queries ≤ T then C (weights k : ℂ) * (paths k).weightPolynomial else 0

theorem cutoffBiasPolynomial_totalDegree {m w : ℕ} {ι : Type*} [Fintype ι]
    (paths : ι → QueryPath m w) (weights : ι → ℝ) (T : ℕ) :
    (cutoffBiasPolynomial paths weights T).totalDegree ≤ 2 * T := by
  apply totalDegree_finsetSum_le
  intro k _
  split_ifs with hk
  · apply (totalDegree_mul _ _).trans
    simp only [totalDegree_C, zero_add]
    exact (paths k).weight_totalDegree.trans (Nat.mul_le_mul_left 2 hk)
  · simp

theorem eval_cutoffBiasPolynomial {m w T : ℕ} {ι : Type*} [Fintype ι]
    (paths : ι → QueryPath m w) (weights : ι → ℝ)
    (hqueries : ∀ (k : ι) (z : BitString m),
      0 < (paths k).bornWeight z → (paths k).queries ≤ T)
    (z : BitString m) :
    eval (bitValue z) (cutoffBiasPolynomial paths weights T) =
      (branchBias paths weights z : ℂ) := by
  classical
  simp only [cutoffBiasPolynomial, map_sum, branchBias, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : (paths k).queries ≤ T
  · simp [hk]
  · have hzero : (paths k).bornWeight z = 0 := by
      apply le_antisymm _ (paths k |>.bornWeight_nonneg z)
      exact le_of_not_gt (fun hp => hk (hqueries k z hp))
    simp [hk, hzero]

/-- Every positive-probability run using at most `T` queries implies the usual
parity obstruction. Unreachable high-query paths are explicitly allowed. -/
theorem reachable_branch_parity_lower_bound {m w T : ℕ} {ι : Type*} [Fintype ι]
    (paths : ι → QueryPath m w) (weights : ι → ℝ)
    (hqueries : ∀ (k : ι) (z : BitString m),
      0 < (paths k).bornWeight z → (paths k).queries ≤ T)
    (hsuccess : ∀ z : BitString m, 0 < paritySign z * branchBias paths weights z) :
    m ≤ 2 * T := by
  have hsign : ∀ z : BitString m,
      0 < paritySign z * (eval (bitValue z) (cutoffBiasPolynomial paths weights T)).re := by
    intro z
    rw [eval_cutoffBiasPolynomial paths weights hqueries]
    exact hsuccess z
  exact (degree_ge_of_strict_parity_sign _ hsign).trans
    (cutoffBiasPolynomial_totalDegree paths weights T)

/-- Exact `some run` form of the unbounded-error parity theorem, for finite
operational branch families: the selected run has strictly positive Born
weight for a concrete input and uses at least `m/2` queries. -/
theorem exists_reachable_parity_hard_run {m w : ℕ} {ι : Type*} [Fintype ι] (hm : 0 < m)
    (paths : ι → QueryPath m w) (weights : ι → ℝ)
    (hsuccess : ∀ z : BitString m, 0 < paritySign z * branchBias paths weights z) :
    ∃ (z : BitString m) (k : ι),
      0 < (paths k).bornWeight z ∧ m ≤ 2 * (paths k).queries := by
  classical
  by_contra hno
  push_neg at hno
  have hqueries : ∀ (k : ι) (z : BitString m),
      0 < (paths k).bornWeight z → (paths k).queries ≤ (m - 1) / 2 := by
    intro k z hp
    have hk := hno z k hp
    omega
  have hbound := reachable_branch_parity_lower_bound paths weights hqueries hsuccess
  omega

end OptimalQLS.LowerBounds
