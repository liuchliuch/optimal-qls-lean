import QuantumChannelStein.Kraus
import QuantumChannelStein.SupportDomination
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.EReal.Basic

/-!
# Finite-state Umegaki relative entropy

This file defines the actual base-two Umegaki relative entropy of finite
density matrices, with values in `EReal`. The value is `⊤` unless the support
of the first state is contained in the support of the second state.

`spectralLog2` uses the finite-spectrum Hermitian functional calculus. Its
value on a zero eigenvalue is zero, the harmless convention used *inside*
the support-aware trace formula. The support test is essential: simply
using the totalized real logarithm in the trace formula for every pair
would incorrectly assign finite values to unsupported pairs.

The results below establish the spectral realization, self-relative
entropy, and the equivalence of finiteness, support inclusion, and finite
positive-semidefinite domination. Nonnegativity, data processing,
additivity, and channel regularization are not asserted here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein
namespace RelativeEntropy

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {n : ℕ}

/-- `support ρ ⊆ support σ`, expressed without choosing eigenvectors, as
reversed kernel inclusion. -/
def supportIncluded (ρ σ : State n) : Prop :=
  LinearMap.ker σ.matrix.mulVecLin ≤ LinearMap.ker ρ.matrix.mulVecLin

@[refl, simp]
theorem supportIncluded_refl (ρ : State n) : supportIncluded ρ ρ := le_rfl

@[trans]
theorem supportIncluded_trans {ρ σ τ : State n}
    (hρσ : supportIncluded ρ σ) (hστ : supportIncluded σ τ) :
    supportIncluded ρ τ := le_trans hστ hρσ

/-- Base-two spectral logarithm of a density matrix, assigning zero on its
kernel. This is an auxiliary matrix for the support-aware definition below,
not an extension that makes unsupported relative entropies finite. -/
def spectralLog2 (ρ : State n) : Operator n :=
  ρ.positive.isHermitian.cfc (Real.logb 2)

/-- The spectral definition agrees with mathlib's continuous functional
calculus: every function on a finite matrix spectrum is continuous. -/
theorem spectralLog2_eq_cfc (ρ : State n) :
    spectralLog2 ρ = cfc (Real.logb 2) ρ.matrix :=
  (ρ.positive.isHermitian.cfc_eq (Real.logb 2)).symm

/-- Explicit diagonalization formula for the base-two matrix logarithm. -/
theorem spectralLog2_eq_spectral (ρ : State n) :
    spectralLog2 ρ =
      (ρ.positive.isHermitian.eigenvectorUnitary : Operator n) *
        Matrix.diagonal (fun i =>
          (Real.logb 2 (ρ.positive.isHermitian.eigenvalues i) : ℂ)) *
        (ρ.positive.isHermitian.eigenvectorUnitary : Operator n)ᴴ := rfl

theorem spectralLog2_isHermitian (ρ : State n) : (spectralLog2 ρ).IsHermitian := by
  rw [spectralLog2_eq_cfc]
  exact IsSelfAdjoint.cfc

/-- The trace in the Umegaki expression is real, although its matrix
product need not itself be Hermitian. -/
theorem traceFormula_im_zero (ρ σ : State n) :
    (ρ.matrix * (spectralLog2 ρ - spectralLog2 σ)).trace.im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  change star (ρ.matrix * (spectralLog2 ρ - spectralLog2 σ)).trace = _
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
    ((spectralLog2_isHermitian ρ).sub (spectralLog2_isHermitian σ)).eq,
    ρ.positive.isHermitian.eq, Matrix.trace_mul_comm]

/-- A functional-calculus trace is a genuine finite spectral sum, with
weights obtained by expressing the first state in the second eigenbasis. -/
theorem trace_mul_cfc_eq_spectral (ρ σ : State n) (f : ℝ → ℝ) :
    (ρ.matrix * cfc f σ.matrix).trace.re =
      ∑ i, (((σ.positive.isHermitian.eigenvectorUnitary : Operator n)ᴴ *
        ρ.matrix * (σ.positive.isHermitian.eigenvectorUnitary : Operator n)) i i).re *
          f (σ.positive.isHermitian.eigenvalues i) := by
  rw [σ.positive.isHermitian.cfc_eq, Matrix.IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  change (ρ.matrix * ((_ * Matrix.diagonal (fun i =>
    (f (σ.positive.isHermitian.eigenvalues i) : ℂ))) * _)).trace.re = _
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.trace_mul_cycle]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  simp only [Matrix.star_eq_conjTranspose, Matrix.mul_assoc]

/-- The logarithmic cross term is the base-two specialization of the
finite spectral formula. -/
theorem trace_mul_spectralLog2 (ρ σ : State n) :
    (ρ.matrix * spectralLog2 σ).trace.re =
      ∑ i, (((σ.positive.isHermitian.eigenvectorUnitary : Operator n)ᴴ *
        ρ.matrix * (σ.positive.isHermitian.eigenvectorUnitary : Operator n)) i i).re *
          Real.logb 2 (σ.positive.isHermitian.eigenvalues i) := by
  rw [spectralLog2_eq_cfc]
  exact trace_mul_cfc_eq_spectral ρ σ (Real.logb 2)

/-- When the supports are nested, a zero eigenvector of the second state
is also annihilated by the first state. -/
theorem mulVec_eigenvector_eq_zero_of_supportIncluded (ρ σ : State n)
    (h : supportIncluded ρ σ) (i : Fin n)
    (hi : σ.positive.isHermitian.eigenvalues i = 0) :
    ρ.matrix *ᵥ ⇑(σ.positive.isHermitian.eigenvectorBasis i) = 0 := by
  change ρ.matrix.mulVecLin ⇑(σ.positive.isHermitian.eigenvectorBasis i) = 0
  apply LinearMap.mem_ker.mp
  apply h
  apply LinearMap.mem_ker.mpr
  change σ.matrix *ᵥ ⇑(σ.positive.isHermitian.eigenvectorBasis i) = 0
  rw [σ.positive.isHermitian.mulVec_eigenvectorBasis, hi, zero_smul]

/-- In a supported pair, the weight of every zero eigenvalue in the
second state's eigenbasis vanishes. -/
theorem eigenbasis_weight_eq_zero_of_supportIncluded (ρ σ : State n)
    (h : supportIncluded ρ σ) (i : Fin n)
    (hi : σ.positive.isHermitian.eigenvalues i = 0) :
    (((σ.positive.isHermitian.eigenvectorUnitary : Operator n)ᴴ *
      ρ.matrix * (σ.positive.isHermitian.eigenvectorUnitary : Operator n)) i i).re = 0 := by
  have hvec :
      ((σ.positive.isHermitian.eigenvectorUnitary : Operator n)ᴴ *
        ρ.matrix * (σ.positive.isHermitian.eigenvectorUnitary : Operator n)) *ᵥ
          Pi.single i 1 = 0 := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      σ.positive.isHermitian.eigenvectorUnitary_mulVec,
      mulVec_eigenvector_eq_zero_of_supportIncluded ρ σ h i hi,
      Matrix.mulVec_zero]
  have hii := congrFun hvec i
  simp only [Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply,
    Pi.zero_apply] at hii
  rw [hii, Complex.zero_re]

/-- On a supported pair the CFC cross trace depends only on values at
strictly positive eigenvalues. In particular, the arbitrary finite value
assigned to `log 0` has no effect on the Umegaki trace formula. -/
theorem trace_mul_cfc_congr_on_positive (ρ σ : State n)
    (h : supportIncluded ρ σ) (f g : ℝ → ℝ)
    (hfg : ∀ x : ℝ, 0 < x → f x = g x) :
    (ρ.matrix * cfc f σ.matrix).trace.re =
      (ρ.matrix * cfc g σ.matrix).trace.re := by
  rw [trace_mul_cfc_eq_spectral, trace_mul_cfc_eq_spectral]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : σ.positive.isHermitian.eigenvalues i = 0
  · rw [eigenbasis_weight_eq_zero_of_supportIncluded ρ σ h i hi]
    simp
  · rw [hfg _ (lt_of_le_of_ne (σ.positive.eigenvalues_nonneg i) (Ne.symm hi))]

/-- The entropy contribution of the first state is the usual eigenvalue
sum, with zero eigenvalues contributing zero. -/
theorem trace_mul_self_spectralLog2 (ρ : State n) :
    (ρ.matrix * spectralLog2 ρ).trace.re =
      ∑ i, ρ.positive.isHermitian.eigenvalues i *
        Real.logb 2 (ρ.positive.isHermitian.eigenvalues i) := by
  rw [trace_mul_spectralLog2]
  have hdiag := ρ.positive.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  simp only [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose] at hdiag
  change (ρ.positive.isHermitian.eigenvectorUnitary : Operator n)ᴴ * ρ.matrix *
    (ρ.positive.isHermitian.eigenvectorUnitary : Operator n) = _ at hdiag
  simp [hdiag]

/-- Real trace formula. This auxiliary real-valued expression is used as
relative entropy only when the support condition holds. -/
def traceFormula (ρ σ : State n) : ℝ :=
  (ρ.matrix * (spectralLog2 ρ - spectralLog2 σ)).trace.re

/-- Spectral evaluation of the finite branch of Umegaki relative entropy. -/
theorem traceFormula_eq_spectral (ρ σ : State n) :
    traceFormula ρ σ =
      (∑ i, ρ.positive.isHermitian.eigenvalues i *
        Real.logb 2 (ρ.positive.isHermitian.eigenvalues i)) -
      ∑ i, (((σ.positive.isHermitian.eigenvectorUnitary : Operator n)ᴴ *
        ρ.matrix * (σ.positive.isHermitian.eigenvectorUnitary : Operator n)) i i).re *
          Real.logb 2 (σ.positive.isHermitian.eigenvalues i) := by
  rw [traceFormula, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re,
    trace_mul_self_spectralLog2, trace_mul_spectralLog2]

/-- Finite-dimensional Umegaki relative entropy in bits, with its correct
infinite value when the first support is not contained in the second. -/
def umegaki (ρ σ : State n) : EReal := by
  classical
  exact if supportIncluded ρ σ then (traceFormula ρ σ : EReal) else ⊤

/-- The finite branch is the base-two logarithmic trace expression. -/
theorem umegaki_of_supportIncluded (ρ σ : State n)
    (h : supportIncluded ρ σ) :
    umegaki ρ σ = (traceFormula ρ σ : EReal) := by
  simp [umegaki, h]

/-- Unsupported pairs have infinite relative entropy, even for singular
states for which the totalized matrix logarithms are finite matrices. -/
theorem umegaki_of_not_supportIncluded (ρ σ : State n)
    (h : ¬ supportIncluded ρ σ) : umegaki ρ σ = ⊤ := by
  simp [umegaki, h]

@[simp]
theorem traceFormula_self (ρ : State n) : traceFormula ρ ρ = 0 := by
  simp [traceFormula]

/-- A state's relative entropy with itself is zero, including singular
states; no invertibility hypothesis is needed. -/
@[simp]
theorem umegaki_self (ρ : State n) : umegaki ρ ρ = 0 := by
  simp [umegaki]

/-- Umegaki relative entropy never takes the value negative infinity. -/
theorem umegaki_ne_bot (ρ σ : State n) : umegaki ρ σ ≠ ⊥ := by
  classical
  by_cases h : supportIncluded ρ σ <;> simp [umegaki, h]

/-- Positive infinity occurs exactly for failure of support inclusion. -/
theorem umegaki_eq_top_iff (ρ σ : State n) :
    umegaki ρ σ = ⊤ ↔ ¬ supportIncluded ρ σ := by
  classical
  by_cases h : supportIncluded ρ σ <;> simp [umegaki, h]

/-- The divergence is finite exactly under the support condition. -/
theorem umegaki_ne_top_iff (ρ σ : State n) :
    umegaki ρ σ ≠ ⊤ ↔ supportIncluded ρ σ := by
  simpa only [not_not] using not_congr (umegaki_eq_top_iff ρ σ)

/-- An order-theoretic version of the finiteness criterion. -/
theorem umegaki_lt_top_iff (ρ σ : State n) :
    umegaki ρ σ < ⊤ ↔ supportIncluded ρ σ := by
  rw [lt_top_iff_ne_top, umegaki_ne_top_iff]

/-- Support inclusion is precisely representability by a real value. -/
theorem umegaki_exists_real_iff (ρ σ : State n) :
    (∃ r : ℝ, umegaki ρ σ = (r : EReal)) ↔ supportIncluded ρ σ := by
  constructor
  · rintro ⟨r, hr⟩
    apply (umegaki_ne_top_iff ρ σ).mp
    rw [hr]
    exact EReal.coe_ne_top r
  · intro h
    exact ⟨traceFormula ρ σ, umegaki_of_supportIncluded ρ σ h⟩

/-- The support condition can equivalently be checked by finite PSD
domination, including singular states. -/
theorem supportIncluded_iff_exists_domination (ρ σ : State n) :
    supportIncluded ρ σ ↔
      ∃ c : ℝ, 1 ≤ c ∧ (c • σ.matrix - ρ.matrix).PosSemidef :=
  SupportDomination.ker_le_iff_exists_domination ρ.positive σ.positive

/-- Finite-state relative entropy is finite exactly when the first state
is dominated by a finite scalar multiple of the second state. -/
theorem umegaki_lt_top_iff_exists_domination (ρ σ : State n) :
    umegaki ρ σ < ⊤ ↔
      ∃ c : ℝ, 1 ≤ c ∧ (c • σ.matrix - ρ.matrix).PosSemidef := by
  rw [umegaki_lt_top_iff, supportIncluded_iff_exists_domination]

/-- Finite scalar domination rules out infinite relative entropy. -/
theorem umegaki_lt_top_of_domination (ρ σ : State n) (c : ℝ)
    (h : (c • σ.matrix - ρ.matrix).PosSemidef) : umegaki ρ σ < ⊤ := by
  apply (umegaki_lt_top_iff ρ σ).mpr
  exact SupportDomination.ker_le_of_posSemidef_smul_sub ρ.positive h

end RelativeEntropy
end QuantumChannelStein
