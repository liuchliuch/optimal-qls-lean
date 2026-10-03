import OptimalQLS.LowerBounds.FiniteProgramChannel
import OptimalQLS.LowerBounds.HaltingInstrument

/-! Exact flagged density semantics of the common finite instruction program. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
universe u v
variable {A : Type u} {B : Type v} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  {d w : ℕ}

theorem flagInjection_conjugation (flag : Bool) (X : Matrix (Fin d) (Fin d) ℂ) :
    flagInjection flag * X * (flagInjection flag).conjTranspose =
      Matrix.fromBlocks (if flag then X else 0) 0 0 (if flag then 0 else X) := by
  cases flag <;> simp [flagInjection, Matrix.fromRows_mul,
    Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromRows_mul_fromCols]
  all_goals ext (i | i) (j | j) <;> rfl

/-- The coherent-channel view and recursive success/failure densities are
proved equal on the actual initial vector, without a representation premise. -/
theorem FiniteOracleProgram.outputChannel_pureDensity (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) :
    (tree.outputChannel UA Ub).apply (pureDensity psi) =
      Matrix.fromBlocks (tree.executeDensity UA Ub id psi) 0 0 (tree.executeDensity UA Ub Bool.not psi) := by
  rw [outputChannel, FiniteChannel.ofKraus_apply]
  have hterm (k : tree.Terminal) :
      tree.outputKraus UA Ub k * pureDensity psi * (tree.outputKraus UA Ub k).conjTranspose =
        Matrix.fromBlocks (if tree.terminalSuccess k then pureDensity ((tree.terminalPath (.initial psi) k).state UA Ub) else 0)
          0 0 (if !(tree.terminalSuccess k) then pureDensity ((tree.terminalPath (.initial psi) k).state UA Ub) else 0) := by
    rw [outputKraus, Matrix.conjTranspose_mul]
    have heq : flagInjection (d := d) (tree.terminalSuccess k) * tree.terminalKraus UA Ub k * pureDensity psi *
        ((tree.terminalKraus UA Ub k).conjTranspose * (flagInjection (d := d) (tree.terminalSuccess k)).conjTranspose) =
        flagInjection (d := d) (tree.terminalSuccess k) * pureDensity (tree.terminalKraus UA Ub k *ᵥ psi) *
          (flagInjection (d := d) (tree.terminalSuccess k)).conjTranspose := by
      rw [pureDensity_mulVec]
      simp only [Matrix.mul_assoc]
    rw [heq, flagInjection_conjugation]
    have hp := tree.terminalKraus_path_state (.initial psi) UA Ub k
    change tree.terminalKraus UA Ub k *ᵥ psi = _ at hp
    rw [hp]
    cases tree.terminalSuccess k <;> rfl
  simp only [hterm]
  rw [sum_fromBlocks]
  simp only [Finset.sum_const_zero]
  have hs := tree.terminalDensity_eq_execute (.initial psi) UA Ub id
  have hf := tree.terminalDensity_eq_execute (.initial psi) UA Ub Bool.not
  simp only [id_eq, VariableQueryPath.state] at hs hf
  rw [hs, hf]

theorem FiniteOracleProgram.executeDensity_positive (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (select : Bool → Bool) (psi : Fin w → ℂ) :
    (tree.executeDensity UA Ub select psi).PosSemidef := by
  have h := tree.terminalDensity_eq_execute (.initial psi) UA Ub select
  simp only [VariableQueryPath.state] at h
  rw [← h]
  exact Finset.sum_induction _ _ (fun _ _ hX hY => hX.add hY) Matrix.PosSemidef.zero
    (fun k _ => by split <;> first | exact pureDensity_positive _ | exact Matrix.PosSemidef.zero)

def FiniteOracleProgram.successProbability (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) : ℝ :=
  (tree.executeDensity UA Ub id psi).trace.re

def FiniteOracleProgram.conditionalOutput (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  (tree.successProbability UA Ub psi)⁻¹ • tree.executeDensity UA Ub id psi

theorem FiniteOracleProgram.successProbability_bounds (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ)
    (hpsi : ‖WithLp.toLp 2 psi‖ = 1) :
    0 ≤ tree.successProbability UA Ub psi ∧ tree.successProbability UA Ub psi ≤ 1 := by
  have hs := (tree.executeDensity_positive UA Ub id psi).trace_nonneg.1
  have hf := (tree.executeDensity_positive UA Ub Bool.not psi).trace_nonneg.1
  have hm := congrArg (fun X : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ => X.trace.re)
    (tree.outputChannel_pureDensity UA Ub psi)
  dsimp only at hm
  rw [FiniteChannel.trace_apply, pureDensity_trace, trace_blockDiagonal] at hm
  simp only [Complex.ofReal_re, Complex.add_re, hpsi, one_pow] at hm
  change 0 ≤ (tree.executeDensity UA Ub id psi).trace.re ∧ _
  norm_num at hs hf
  exact ⟨hs, by dsimp only [successProbability]; linarith⟩

theorem FiniteOracleProgram.successDensity_eq_probability_smul (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ)
    (hp : 0 < tree.successProbability UA Ub psi) :
    tree.executeDensity UA Ub id psi = tree.successProbability UA Ub psi • tree.conditionalOutput UA Ub psi := by
  rw [conditionalOutput, smul_smul, mul_inv_cancel₀ hp.ne', one_smul]

end OptimalQLS.LowerBounds
