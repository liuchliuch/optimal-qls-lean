import OptimalQLS.LowerBounds.FiniteProgramDensity
import OptimalQLS.LowerBounds.VariableMatrixLowerBound

/-!
# Literal diagonal-observable parity decoder for the common instruction tree

The decoder appends a computational-basis measurement to every terminal path.
Success leaves use the fixed observable's diagonal weight; failure contributes
zero bias. Exact density and Born identities connect this to the polynomial
method. The history-family observable is diagonal in precisely this sense.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
universe u v
variable {A : Type u} {B : Type v} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  {d w : ℕ}

def coordinateProjection (i : Fin d) : Matrix (Fin d) (Fin d) ℂ := Matrix.diagonal (fun j => if j = i then 1 else 0)

theorem coordinateProjection_bornMass (i : Fin d) (psi : Fin d → ℂ) :
    bornMass (coordinateProjection i *ᵥ psi) = Complex.normSq (psi i) := by
  simp [coordinateProjection, bornMass, Matrix.mulVec_diagonal, apply_ite]

def FiniteOracleProgram.decoderPath (tree : FiniteOracleProgram A B d w) (psi : Fin w → ℂ)
    (k : tree.Terminal × Fin d) : VariableQueryPath A B d :=
  .work (coordinateProjection k.2) (tree.terminalPath (.initial psi) k.1)

def FiniteOracleProgram.decoderWeight (tree : FiniteOracleProgram A B d w) (weights : Fin d → ℝ)
    (k : tree.Terminal × Fin d) : ℝ := if tree.terminalSuccess k.1 then weights k.2 else 0

theorem FiniteOracleProgram.decoderPath_bornWeight (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ)
    (k : tree.Terminal × Fin d) :
    (tree.decoderPath psi k).bornWeight UA Ub = Complex.normSq ((tree.terminalPath (.initial psi) k.1).state UA Ub k.2) :=
  coordinateProjection_bornMass _ _

theorem FiniteOracleProgram.decoder_mass (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) :
    (∑ k : tree.Terminal × Fin d, (tree.decoderPath psi k).bornWeight UA Ub) = bornMass psi := by
  rw [Fintype.sum_prod_type]
  simp only [tree.decoderPath_bornWeight]
  exact tree.terminalBorn_sum UA Ub psi

/-- The probability bias of the actual appended decoder equals the fixed
observable expectation on the actual unnormalized successful density. -/
theorem FiniteOracleProgram.decoder_bias (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) (weights : Fin d → ℝ) :
    (∑ k : tree.Terminal × Fin d, tree.decoderWeight weights k * (tree.decoderPath psi k).bornWeight UA Ub) =
      (Matrix.diagonal (fun i => (weights i : ℂ)) * tree.executeDensity UA Ub id psi).trace.re := by
  have hd := tree.terminalDensity_eq_execute (.initial psi) UA Ub id
  simp only [id_eq, VariableQueryPath.state] at hd
  rw [← hd, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hs : tree.terminalSuccess k = true
  · simp only [decoderWeight, hs, if_true, tree.decoderPath_bornWeight,
      pureDensity_expectation, pureExpectation_diagonal, Complex.normSq_eq_norm_sq]
  · simp [decoderWeight, hs]

theorem FiniteOracleProgram.decoder_weight_bound (tree : FiniteOracleProgram A B d w)
    (weights : Fin d → ℝ) (hw : ∀ i, |weights i| ≤ 1) : ∀ k, |tree.decoderWeight weights k| ≤ 1 := by
  intro k
  unfold decoderWeight
  split <;> simp_all

/-- Matrix hardness for the same actual program, from its successful output
expectation. Kraus completeness supplies all branch-mass hypotheses. -/
theorem FiniteOracleProgram.diagonal_decoder_matrix_hard_run {m : ℕ}
    (tree : FiniteOracleProgram A B d w) (P : Matrix A A (InputPolynomial m)) (hdegree : MatrixDegreeLE P 1)
    (UA : BitString m → Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (heval : ∀ z, evalMatrix z P = (UA z : Matrix A A ℂ))
    (psi : Fin w → ℂ) (hpsi : ‖WithLp.toLp 2 psi‖ = 1)
    (weights : Fin d → ℝ) (hw : ∀ i, |weights i| ≤ 1)
    (hsign : ∀ z, 0 < paritySign z *
      (Matrix.diagonal (fun i => (weights i : ℂ)) * tree.executeDensity (UA z) Ub id psi).trace.re) :
    ∃ (z : BitString m) (k : tree.Terminal),
      0 < (tree.terminalPath (.initial psi) k).bornWeight (UA z) Ub ∧
        m ≤ 2 * (tree.terminalPath (.initial psi) k).matrixQueries := by
  classical
  have hmass (z : BitString m) (s : Finset (tree.Terminal × Fin d)) :
      (∑ k ∈ s, (tree.decoderPath psi k).bornWeight (UA z) Ub) ≤ 1 := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun k _ _ => (tree.decoderPath psi k).bornWeight_nonneg (UA z) Ub)).trans
    rw [tree.decoder_mass, bornMass_eq_norm_sq, hpsi]
    norm_num
  have hbias (z : BitString m) : countableVariableBias (fun _ : tree.Terminal × Fin d => d)
      (tree.decoderPath psi) (tree.decoderWeight weights) UA Ub z =
      (Matrix.diagonal (fun i => (weights i : ℂ)) * tree.executeDensity (UA z) Ub id psi).trace.re := by
    rw [countableVariableBias, tsum_fintype]
    exact tree.decoder_bias (UA z) Ub psi weights
  obtain ⟨z, k, hborn, hqueries⟩ := countable_variable_matrix_hard_run P hdegree UA Ub heval
    (fun _ : tree.Terminal × Fin d => d) (tree.decoderPath psi) (tree.decoderWeight weights)
    (tree.decoder_weight_bound weights hw) hmass (fun z => by rw [hbias]; exact hsign z)
  refine ⟨z, k.1, ?_, hqueries⟩
  rw [tree.decoderPath_bornWeight] at hborn
  apply hborn.trans_le
  exact Finset.single_le_sum (fun i _ => Complex.normSq_nonneg _) (Finset.mem_univ k.2)

end OptimalQLS.LowerBounds
