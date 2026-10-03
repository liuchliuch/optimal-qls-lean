import OptimalQLS.LowerBounds.VariableQueryPolynomial

/-!
# Matrix-query hardness allowing workspace changes inside each branch

This applies the proved degree-one representation of the *full* matrix oracle,
including controlled/adjoint ports, to actual two-oracle terminal paths.
Vector calls use the one fixed full preparation oracle and are uncharged in
this argument. Countably many terminal branches and unbounded stopping times
are allowed under finite-partial Born mass≤1.

The final solver-to-parity decoder still needs its trace-error/success guarantee
bridge; here strict parity agreement is stated on the literal terminal bias.
-/
noncomputable section
open scoped BigOperators
namespace OptimalQLS.LowerBounds
open Matrix

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def countableVariableBias {m : ℕ} {ι : Type*} (w : ι → ℕ)
    (paths : ∀ k, VariableQueryPath A B (w k)) (weights : ι → ℝ)
    (UA : BitString m → Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (z : BitString m) : ℝ :=
  ∑' k, weights k * (paths k).bornWeight (UA z) Ub

theorem variable_signed_summable {m : ℕ} {ι : Type*} (w : ι → ℕ)
    (paths : ∀ k, VariableQueryPath A B (w k)) (weights : ι → ℝ)
    (UA : BitString m → Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (hweights : ∀ k, |weights k| ≤ 1) (z : BitString m)
    (hmass : ∀ s : Finset ι, ∑ k ∈ s, (paths k).bornWeight (UA z) Ub ≤ 1) :
    Summable (fun k => weights k * (paths k).bornWeight (UA z) Ub) := by
  have hs : Summable (fun k => (paths k).bornWeight (UA z) Ub) :=
    summable_of_sum_le (fun k => (paths k).bornWeight_nonneg (UA z) Ub) hmass
  apply hs.of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ((paths k).bornWeight_nonneg (UA z) Ub)]
  exact mul_le_of_le_one_left ((paths k).bornWeight_nonneg (UA z) Ub) (hweights k)

/-- Operational matrix-query lower bound for a concretely represented degree-one
oracle. It is later specialized to the derived hard-family polynomial. -/
theorem countable_variable_matrix_hard_run {m : ℕ} {ι : Type*} [Countable ι]
    (P : Matrix A A (InputPolynomial m)) (hdegree : MatrixDegreeLE P 1)
    (UA : BitString m → Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (heval : ∀ z, evalMatrix z P = (UA z : Matrix A A ℂ))
    (w : ι → ℕ) (paths : ∀ k, VariableQueryPath A B (w k)) (weights : ι → ℝ)
    (hweights : ∀ k, |weights k| ≤ 1)
    (hmass : ∀ (z : BitString m) (s : Finset ι), ∑ k ∈ s, (paths k).bornWeight (UA z) Ub ≤ 1)
    (hsuccess : ∀ z : BitString m, 0 < paritySign z * countableVariableBias w paths weights UA Ub z) :
    ∃ (z : BitString m) (k : ι),
      0 < (paths k).bornWeight (UA z) Ub ∧ m ≤ 2 * (paths k).matrixQueries := by
  classical
  by_contra hno
  push_neg at hno
  have hbranch : ∀ k : ι,
      (∑ z : BitString m, paritySign z * (weights k * (paths k).bornWeight (UA z) Ub)) = 0 := by
    intro k
    by_cases hshort : 2 * (paths k).matrixQueries < m
    · exact (paths k).short_parity_sum_zero P hdegree UA Ub heval (weights k) hshort
    · have hlong : m ≤ 2 * (paths k).matrixQueries := by omega
      apply Finset.sum_eq_zero
      intro z _
      have hz : (paths k).bornWeight (UA z) Ub = 0 := by
        apply le_antisymm _ ((paths k).bornWeight_nonneg (UA z) Ub)
        exact le_of_not_gt (fun hp => (not_le.mpr (hno z k hp)) hlong)
      simp [hz]
  have hsum (z : BitString m) : Summable (fun k => weights k * (paths k).bornWeight (UA z) Ub) :=
    variable_signed_summable w paths weights UA Ub hweights z (hmass z)
  have hzero : (∑ z : BitString m, paritySign z * countableVariableBias w paths weights UA Ub z) = 0 := by
    calc
      _ = ∑ z : BitString m, ∑' k, paritySign z * (weights k * (paths k).bornWeight (UA z) Ub) := by
        apply Finset.sum_congr rfl
        intro z _
        exact ((hsum z).tsum_mul_left (paritySign z)).symm
      _ = ∑' k, ∑ z : BitString m, paritySign z * (weights k * (paths k).bornWeight (UA z) Ub) :=
        (Summable.tsum_finsetSum (fun z _ => (hsum z).mul_left (paritySign z))).symm
      _ = 0 := by simp [hbranch]
  have hpositive : 0 < ∑ z : BitString m, paritySign z * countableVariableBias w paths weights UA Ub z :=
    Finset.sum_pos (fun z _ => hsuccess z) Finset.univ_nonempty
  rw [hzero] at hpositive
  exact lt_irrefl 0 hpositive

/-- Concrete-family matrix hardness. No oracle polynomial-degree hypothesis
appears here: the full representation and degree are already proved for UA,z.
Every output branch is an actual finite matrix/Kraus and two-oracle path. -/
theorem hard_family_variable_matrix_query_lower_bound {N m : ℕ} [NeZero N] [NeZero m]
    {kappa estimate : ℝ} (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) {ι : Type*} [Countable ι]
    (w : ι → ℕ)
    (paths : ∀ k, VariableQueryPath (Bool × HardFamilyIndex N) (HardFamilyIndex N) (w k))
    (weights : ι → ℝ) (hweights : ∀ k, |weights k| ≤ 1)
    (hmass : ∀ (z : BitString m) (s : Finset ι),
      ∑ k ∈ s, (paths k).bornWeight (hardFamilyEncoding (N := N) hk z)
        (hardFamilyPreparation hk he hek hN) ≤ 1)
    (hsuccess : ∀ z : BitString m, 0 < paritySign z * countableVariableBias w paths weights
      (fun z => hardFamilyEncoding (N := N) hk z) (hardFamilyPreparation hk he hek hN) z) :
    ∃ (z : BitString m) (k : ι),
      0 < (paths k).bornWeight (hardFamilyEncoding (N := N) hk z) (hardFamilyPreparation hk he hek hN) ∧
        m ≤ 2 * (paths k).matrixQueries :=
  countable_variable_matrix_hard_run (hardFamilyPolynomial hk hN) (hardFamilyPolynomial_degree hk hN)
    (fun z => hardFamilyEncoding (N := N) hk z) (hardFamilyPreparation hk he hek hN)
    (hardFamilyPolynomial_eval hk hN) w paths weights hweights hmass hsuccess

end OptimalQLS.LowerBounds
