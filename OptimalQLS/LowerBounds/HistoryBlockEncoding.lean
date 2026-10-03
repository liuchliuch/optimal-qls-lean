import OptimalQLS.LowerBounds.ParityHistoryFamily
import OptimalQLS.BlockEncoding
import OptimalQLS.FractionalTransducer

/-!
# Exact one-signal-qubit LCU for the actual cyclic history matrix

The encoding is an explicitly constructed unitary: a real signal mixing,
controlled negative history permutation, and the same mixing. Compression
is proved entrywise to equal `(I-lambda B)/(1+lambda)` exactly. No block-encoding
existence assumption is used.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix

variable {D : Type*} [Fintype D] [DecidableEq D]

def sumBoolEquiv (D : Type*) : (D ⊕ D) ≃ Bool × D where
  toFun x := match x with | .inl d => (false, d) | .inr d => (true, d)
  invFun x := if x.1 then .inr x.2 else .inl x.2
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨s, d⟩; cases s <;> rfl

def negativeUnitary (U : Matrix.unitaryGroup D ℂ) : Matrix.unitaryGroup D ℂ :=
  ⟨-(U : Matrix D D ℂ), by
    rw [Matrix.mem_unitaryGroup_iff]
    simpa using U.property.2⟩

/-- Explicit mixing-select-mixing LCU, with one Boolean signal register. -/
def twoTermLCU (U : Matrix.unitaryGroup D ℂ) (r : ℝ) (hr : |r| < 1) :
    Matrix.unitaryGroup (Bool × D) ℂ :=
  OptimalQLS.rewireUnitary (sumBoolEquiv D)
    (⟨OptimalQLS.fractionalMix r, OptimalQLS.fractionalMix_unitary hr⟩ *
      OptimalQLS.privateOracle (negativeUnitary U) *
      ⟨OptimalQLS.fractionalMix r, OptimalQLS.fractionalMix_unitary hr⟩)

/-- Exact two-term compression, with coefficients derived from the real mixing. -/
theorem twoTermLCU_block (U : Matrix.unitaryGroup D ℂ) (r : ℝ) (hr : |r| < 1) :
    OptimalQLS.signalBlock false (twoTermLCU U r hr : Matrix (Bool × D) (Bool × D) ℂ) =
      r ^ 2 • (1 : Matrix D D ℂ) - (1 - r ^ 2) • (U : Matrix D D ℂ) := by
  have hsq : Real.sqrt (1 - r ^ 2) * Real.sqrt (1 - r ^ 2) = 1 - r ^ 2 :=
    Real.mul_self_sqrt (by nlinarith [(abs_lt.mp hr).1, (abs_lt.mp hr).2])
  ext i j
  rw [OptimalQLS.signalBlock_entries]
  change ((OptimalQLS.fractionalMix (n := D) r *
    Matrix.fromBlocks 1 0 0 (-(U : Matrix D D ℂ)) * OptimalQLS.fractionalMix (n := D) r) :
      Matrix (D ⊕ D) (D ⊕ D) ℂ) (Sum.inl i) (Sum.inl j) = _
  rw [OptimalQLS.fractionalMix, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, zero_add, add_zero,
    mul_smul_comm, smul_mul_assoc, smul_smul, smul_neg, smul_zero, neg_neg,
    Matrix.fromBlocks_apply₁₁]
  rw [hsq]
  have hr2 : (-r) * (-r) = r ^ 2 := by ring
  rw [hr2]
  rfl

def lcuMixingParameter (lam : ℝ) : ℝ := Real.sqrt ((1 + lam)⁻¹)

theorem lcuMixingParameter_bound {lam : ℝ} (hpos : 0 < lam) : |lcuMixingParameter lam| < 1 := by
  have hp : 0 < 1 + lam := by linarith
  have hi : (1 + lam)⁻¹ < (1 : ℝ) := (inv_lt_one₀ hp).mpr (by linarith)
  have hs : lcuMixingParameter lam ^ 2 = (1 + lam)⁻¹ := Real.sq_sqrt (inv_nonneg.mpr hp.le)
  have hn : 0 ≤ lcuMixingParameter lam := Real.sqrt_nonneg _
  rw [abs_of_nonneg hn]
  nlinarith

def historyStepUnitary {N : ℕ} [NeZero N] (profile : Fin N → Bool) :
    Matrix.unitaryGroup (HistoryBasis N) ℂ :=
  ⟨historyStep profile, Matrix.mem_unitaryGroup_iff'.mpr (historyStep_unitary profile)⟩

/-- Concrete exact encoding using one signal qubit. -/
def historyBlockEncoding {N : ℕ} [NeZero N] (profile : Fin N → Bool)
    (lam : ℝ) (hpos : 0 < lam) : Matrix.unitaryGroup (Bool × HistoryBasis N) ℂ :=
  twoTermLCU (historyStepUnitary profile) (lcuMixingParameter lam) (lcuMixingParameter_bound hpos)

theorem historyBlockEncoding_signalBlock {N : ℕ} [NeZero N] (profile : Fin N → Bool)
    (lam : ℝ) (hpos : 0 < lam) :
    OptimalQLS.signalBlock false (historyBlockEncoding profile lam hpos :
      Matrix (Bool × HistoryBasis N) (Bool × HistoryBasis N) ℂ) = historyMatrix profile (lam : ℂ) := by
  have hp : 0 < 1 + lam := by linarith
  have hs : lcuMixingParameter lam ^ 2 = (1 + lam)⁻¹ := Real.sq_sqrt (inv_nonneg.mpr hp.le)
  rw [historyBlockEncoding, twoTermLCU_block, hs]
  ext i j
  simp only [historyStepUnitary, historyMatrix, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, RCLike.real_smul_eq_coe_mul, Complex.ofReal_inv, Complex.ofReal_add,
    Complex.ofReal_one, Complex.ofReal_sub, Pi.smul_apply]
  push_cast
  have hpc : (1 : ℂ) + (lam : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp [hpc]
  ring_nf
  simp [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]
  abel

theorem historyBlockEncoding_exact {N : ℕ} [NeZero N] (profile : Fin N → Bool)
    (lam : ℝ) (hpos : 0 < lam) :
    OptimalQLS.IsBlockEncoding false 1 0 (historyBlockEncoding profile lam hpos)
      (historyMatrix profile (lam : ℂ)) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [one_smul, historyBlockEncoding_signalBlock]
  simp

end OptimalQLS.LowerBounds
