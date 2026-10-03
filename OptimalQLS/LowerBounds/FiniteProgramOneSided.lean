import OptimalQLS.LowerBounds.ProgramCutDistance
import OptimalQLS.LowerBounds.ProgramAbortProbability

/-!
# Original-input one-sided hybrid in the common instruction semantics

Both the polynomial terminal paths and this stopping argument are derived
from the very same program. Finite register dimensions, classical branch
choices and query adjoints may vary arbitrarily through the tree.
-/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
universe u v
variable {A : Type u} {B : Type v} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  {d w : ℕ}

theorem FiniteOracleProgram.truncated_vector_hybrid (tree : FiniteOracleProgram A B d w)
    (out : Fin d) (q : ℕ) (UA : Matrix.unitaryGroup A ℂ) (U V : Matrix.unitaryGroup B ℂ)
    (psi : Fin w → ℂ) (hpsi : ‖WithLp.toLp 2 psi‖ = 1) :
    traceDistance ((tree.truncateVectors out q).markedOutput UA U psi)
      ((tree.truncateVectors out q).markedOutput UA V psi) ≤
      (q : ℝ) * ‖(U : Matrix B B ℂ) - (V : Matrix B B ℂ)‖ := by
  have ht : (pureDensity psi).trace = 1 := by rw [pureDensity_trace, hpsi]; norm_num
  have h := (tree.truncateVectors out q).markedOutputChannel_vector_hybrid UA U V (pureDensity psi)
    (pureDensity_positive psi) ht
  exact h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast tree.truncateVectors_depth out q) (norm_nonneg _))

/-- Only positive-Born runs of the original oracle are bounded. There is no
perturbed-oracle budget assumption and no independent causal representation. -/
theorem FiniteOracleProgram.one_sided_vector_hybrid (tree : FiniteOracleProgram A B d w)
    (hclean : tree.Clean) (out : Fin d) (q : ℕ)
    (UA : Matrix.unitaryGroup A ℂ) (U V : Matrix.unitaryGroup B ℂ)
    (psi : Fin w → ℂ) (hpsi : ‖WithLp.toLp 2 psi‖ = 1)
    (hq : tree.PointwiseVectorBound UA U psi q) :
    traceDistance (tree.markedOutput UA U psi) (tree.markedOutput UA V psi) ≤
      3 * (q : ℝ) * ‖(U : Matrix B B ℂ) - (V : Matrix B B ℂ)‖ := by
  let delta := ‖(U : Matrix B B ℂ) - (V : Matrix B B ℂ)‖
  have hzero := tree.cutMass_zero_of_pointwise_bound UA U psi q hq
  have hold := tree.truncation_distance out q UA U psi
  rw [hzero] at hold
  have hnew := tree.truncation_distance out q UA V psi
  have htrunc := tree.truncated_vector_hybrid out q UA U V psi hpsi
  have habort := bounded_observable_difference (markedAbortProjection (d := d))
    ((tree.truncateVectors out q).markedOutput UA V psi)
    ((tree.truncateVectors out q).markedOutput UA U psi) markedAbortProjection_norm_le
  change |(tree.truncateVectors out q).abortProbability UA V psi -
    (tree.truncateVectors out q).abortProbability UA U psi| ≤ _ at habort
  rw [tree.truncation_abortProbability hclean, tree.truncation_abortProbability hclean,
    hzero, sub_zero, traceDistance_symm] at habort
  have hcut : tree.cutMass UA V q psi ≤ 2 * (q : ℝ) * delta :=
    (le_abs_self _).trans (habort.trans (by dsimp [delta]; linarith))
  have htri₁ := traceDistance_triangle (tree.markedOutput UA U psi)
    ((tree.truncateVectors out q).markedOutput UA U psi) (tree.markedOutput UA V psi)
  have htri₂ := traceDistance_triangle ((tree.truncateVectors out q).markedOutput UA U psi)
    ((tree.truncateVectors out q).markedOutput UA V psi) (tree.markedOutput UA V psi)
  rw [traceDistance_symm ((tree.truncateVectors out q).markedOutput UA V psi)] at htri₂
  change traceDistance (tree.markedOutput UA U psi) (tree.markedOutput UA V psi) ≤ 3 * (q : ℝ) * delta
  change traceDistance ((tree.truncateVectors out q).markedOutput UA U psi)
    ((tree.truncateVectors out q).markedOutput UA V psi) ≤ (q : ℝ) * delta at htrunc
  linarith

end OptimalQLS.LowerBounds
