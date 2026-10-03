import OptimalQLS.LowerBounds.FiniteCoordinates
import OptimalQLS.LowerBounds.ProgramSolverGuarantee

/-! The explicit hard-family diagonal observable in the program output basis. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix

def hardBasisWeight {N m : ℕ} {kappa : ℝ} (hk : 4 ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) : HardFamilyIndex N → ℝ
  | .inl _ => 0
  | .inr (.inl _) => 0
  | .inr (.inr (.inl b)) => if b.1 ∈ tailClockSet (historyPadding_pos hk)
      (show 2 * historyPadding kappa + m ≤ N by omega) then boolSign b.2 else 0
  | .inr (.inr (.inr _)) => 0

theorem hardFamilyObservable_diagonal {N m : ℕ} {kappa : ℝ} (hk : 4 ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) :
    hardFamilyObservable hk hN = Matrix.diagonal (fun i => (hardBasisWeight hk hN i : ℂ)) := by
  ext i j
  rcases i with i | (_ | (i | _)) <;> rcases j with j | (_ | (j | _)) <;>
    simp [hardFamilyObservable, dilatedObservable, augmentedObservable, historyObservable, hardBasisWeight, Matrix.diagonal]
  all_goals split_ifs <;> simp_all

theorem hardBasisWeight_bound {N m : ℕ} {kappa : ℝ} (hk : 4 ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) : ∀ i, |hardBasisWeight hk hN i| ≤ 1 := by
  rintro (i | (_ | (i | _))) <;> simp only [hardBasisWeight]
  · norm_num
  · norm_num
  · split <;> cases i.2 <;> norm_num [boolSign]
  · norm_num

def hardOutputWeight {N m : ℕ} {kappa : ℝ} (hk : 4 ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) : Fin (hardOutputDimension N) → ℝ :=
  hardBasisWeight hk hN ∘ hardOutputCoordinates N

theorem hardOutputWeight_bound {N m : ℕ} {kappa : ℝ} (hk : 4 ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) : ∀ i, |hardOutputWeight hk hN i| ≤ 1 :=
  fun i => hardBasisWeight_bound hk hN _

theorem hardOutput_diagonal {N m : ℕ} {kappa : ℝ} (hk : 4 ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) :
    Matrix.diagonal (fun i => (hardOutputWeight hk hN i : ℂ)) =
      (hardFamilyObservable hk hN).submatrix (hardOutputCoordinates N) (hardOutputCoordinates N) := by
  rw [hardFamilyObservable_diagonal, Matrix.submatrix_diagonal_equiv]
  rfl


theorem hardOutput_signal {N m : ℕ} [NeZero N] {kappa estimate : ℝ}
    (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) (z : BitString m) :
    (5 / 2304 : ℝ) * historyLambda kappa ^ (2 * m) ≤ paritySign z *
      (Matrix.diagonal (fun i => (hardOutputWeight hk hN i : ℂ)) * pureDensity (hardOutputSolution N kappa estimate z)).trace.re := by
  rw [hardOutput_diagonal, hardOutputSolution, pureDensity_reindex, expectation_reindex]
  exact hardFamily_density_signal hk he hek hN z

/-- The concrete hard-family matrix lower bound now starts from actual solver
correctness on one literal varying-workspace instruction tree. -/
theorem FiniteOracleProgram.hard_family_matrix_hard_run {N m : ℕ} [NeZero N] [NeZero m]
    {kappa estimate eps : ℝ} (hk : 4 ≤ kappa) (he : 1 ≤ estimate) (hek : estimate ≤ kappa)
    (hN : N = 2 * historyPadding kappa + 2 * m) {w : ℕ}
    (tree : FiniteOracleProgram (Bool × HardFamilyIndex N) (HardFamilyIndex N) (hardOutputDimension N) w)
    (psi : Fin w → ℂ) (hpsi : ‖WithLp.toLp 2 psi‖ = 1)
    (hgap : 2 * eps < (5 / 2304 : ℝ) * historyLambda kappa ^ (2 * m))
    (hsolve : ∀ z : BitString m, tree.Solves (hardFamilyEncoding (N := N) hk z) (hardFamilyPreparation hk he hek hN)
      psi (hardOutputSolution N kappa estimate z) eps) :
    ∃ (z : BitString m) (k : tree.Terminal),
      0 < (tree.terminalPath (.initial psi) k).bornWeight (hardFamilyEncoding (N := N) hk z) (hardFamilyPreparation hk he hek hN) ∧
        m ≤ 2 * (tree.terminalPath (.initial psi) k).matrixQueries :=
  tree.matrix_hard_run_of_solver (hardFamilyPolynomial hk hN) (hardFamilyPolynomial_degree hk hN)
    (fun z => hardFamilyEncoding (N := N) hk z) (hardFamilyPreparation hk he hek hN)
    (hardFamilyPolynomial_eval hk hN) psi hpsi (hardOutputSolution N kappa estimate)
    (hardOutputWeight hk hN) (hardOutputWeight_bound hk hN) hgap hsolve
    (fun z => hardOutput_signal hk he hek hN z)

end OptimalQLS.LowerBounds
