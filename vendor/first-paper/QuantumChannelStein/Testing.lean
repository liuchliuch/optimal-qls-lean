import QuantumChannelStein.Stinespring
import QuantumChannelStein.TensorNorm
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Effects, acceptance probabilities and square-root tests

Concrete finite-dimensional matrix tests from §2.1 and the preparation for
Lemma 3.4. Matrix norms in this file are the Hilbert L2 operator norms.
-/
set_option maxHeartbeats 800000
noncomputable section
namespace QuantumChannelStein
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
open Matrix

/-- The trace pairing of two positive matrices is nonnegative, even when their
product is not Hermitian. -/
theorem trace_mul_nonnegative {n : ℕ} {A B : Operator n}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  change A = Cᴴ * C at hC
  rw [hC, Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
  exact (hB.mul_mul_conjTranspose_same C).trace_nonneg

namespace Effect
variable {n : ℕ}

/-- Probability of accepting this effect in a density matrix. -/
def probability (T : Effect n) (ρ : State n) : ℝ := (T.matrix * ρ.matrix).trace.re

theorem probability_nonneg (T : Effect n) (ρ : State n) : 0 ≤ T.probability ρ := by
  exact (Complex.nonneg_iff.mp (trace_mul_nonnegative T.positive ρ.positive)).1

theorem probability_le_one (T : Effect n) (ρ : State n) : T.probability ρ ≤ 1 := by
  have h := trace_mul_nonnegative T.complement_positive ρ.positive
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, ρ.trace_one] at h
  have hre := (Complex.nonneg_iff.mp h).1
  simpa [probability] using hre

/-- Positive square root representing the acceptance amplitude. -/
def sqrtMatrix (T : Effect n) : Operator n := CFC.sqrt T.matrix

theorem sqrtMatrix_positive (T : Effect n) : T.sqrtMatrix.PosSemidef :=
  (CFC.sqrt_nonneg T.matrix).posSemidef

theorem sqrtMatrix_mul_self (T : Effect n) : T.sqrtMatrix * T.sqrtMatrix = T.matrix :=
  CFC.sqrt_mul_sqrt_self T.matrix T.positive.nonneg

theorem norm_matrix_le_one (T : Effect n) : ‖T.matrix‖ ≤ 1 := by
  letI : CStarAlgebra (Operator n) := CStarAlgebra.mk
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg T.matrix T.positive.nonneg).mpr
  exact T.complement_positive

/-- The square root of a binary effect is a Hilbert-space contraction. -/
theorem norm_sqrtMatrix_le_one (T : Effect n) : ‖T.sqrtMatrix‖ ≤ 1 := by
  have hsq : ‖T.sqrtMatrix‖ * ‖T.sqrtMatrix‖ = ‖T.matrix‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self,
      T.sqrtMatrix_positive.isHermitian.eq, T.sqrtMatrix_mul_self]
  have hnorm := T.norm_matrix_le_one
  have hnonneg := norm_nonneg T.sqrtMatrix
  nlinarith

end Effect

/-- Unnormalized pure-state density matrix. -/
def pureMatrix {ι : Type*} [Fintype ι] (x : EuclideanSpace ℂ ι) : Matrix ι ι ℂ :=
  Matrix.vecMulVec (WithLp.ofLp x) (star (WithLp.ofLp x))

/-- Pure-state trace equals squared Hilbert norm. -/
theorem trace_pureMatrix_re {ι : Type*} [Fintype ι] (x : EuclideanSpace ℂ ι) :
    (pureMatrix x).trace.re = ‖x‖ ^ 2 := by
  simp [pureMatrix, Matrix.trace_vecMulVec, dotProduct, EuclideanSpace.norm_sq_eq,
    ← Complex.normSq_eq_norm_sq, Complex.mul_conj]

/-- Conjugating a pure density matrix is equivalent to applying the matrix to
its state vector. -/
theorem conjugate_pureMatrix {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix κ ι ℂ) (x : EuclideanSpace ℂ ι) :
    A * pureMatrix x * Aᴴ = pureMatrix (WithLp.toLp 2 (A *ᵥ WithLp.ofLp x)) := by
  simp [pureMatrix, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.vecMul_conjTranspose]

/-- The quadratic acceptance weight equals the squared post-test norm. -/
theorem pure_acceptance_eq_norm_sq {n : ℕ} (T : Effect n)
    (x : EuclideanSpace ℂ (Fin n)) :
    (T.matrix * pureMatrix x).trace.re =
      ‖WithLp.toLp 2 (T.sqrtMatrix *ᵥ WithLp.ofLp x)‖ ^ 2 := by
  rw [← trace_pureMatrix_re, ← conjugate_pureMatrix,
    T.sqrtMatrix_positive.isHermitian.eq, Matrix.trace_mul_cycle]
  rw [T.sqrtMatrix_mul_self]


/-- The Born weight for the positive test `SᴴS` is the squared output norm. -/
theorem trace_test_pure_eq_norm_sq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : Matrix κ ι ℂ) (x : EuclideanSpace ℂ ι) :
    ((Sᴴ * S) * pureMatrix x).trace.re =
      ‖WithLp.toLp 2 (S *ᵥ WithLp.ofLp x)‖ ^ 2 := by
  rw [← trace_pureMatrix_re, ← conjugate_pureMatrix]
  exact congrArg Complex.re (Matrix.trace_mul_cycle S (pureMatrix x) Sᴴ).symm

/-- Partial trace is dual to extending the measured operator by the identity. -/
theorem trace_partialTrace_duality {b e : ℕ} (T : Operator b)
    (X : Matrix (Fin b × Fin e) (Fin b × Fin e) ℂ) :
    (T * KrausChannel.traceEnvironment X).trace =
      (((T ⊗ₖ (1 : Operator e)) * X).trace) := by
  simp [KrausChannel.traceEnvironment, Matrix.trace, Matrix.mul_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]

/-- Acceptance probability from a possibly unnormalized dilation vector. -/
def dilationAcceptance {b e : ℕ} (T : Effect b)
    (x : EuclideanSpace ℂ (Fin b × Fin e)) : ℝ :=
  (T.matrix * KrausChannel.traceEnvironment (pureMatrix x)).trace.re

/-- The probability formula is exactly the squared square-root-test amplitude. -/
theorem dilationAcceptance_eq_norm_sq {b e : ℕ} (T : Effect b)
    (x : EuclideanSpace ℂ (Fin b × Fin e)) :
    dilationAcceptance T x =
      ‖WithLp.toLp 2 ((T.sqrtMatrix ⊗ₖ (1 : Operator e)) *ᵥ WithLp.ofLp x)‖ ^ 2 := by
  unfold dilationAcceptance
  rw [trace_partialTrace_duality, ← trace_test_pure_eq_norm_sq]
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    T.sqrtMatrix_positive.isHermitian.eq, ← Matrix.mul_kronecker_mul,
    T.sqrtMatrix_mul_self, Matrix.one_mul]

/-- Taking the square root recovers the acceptance amplitude without any
additional positivity assumption on the scalar probability. -/
theorem sqrt_dilationAcceptance {b e : ℕ} (T : Effect b)
    (x : EuclideanSpace ℂ (Fin b × Fin e)) :
    Real.sqrt (dilationAcceptance T x) =
      ‖WithLp.toLp 2 ((T.sqrtMatrix ⊗ₖ (1 : Operator e)) *ᵥ WithLp.ofLp x)‖ := by
  rw [dilationAcceptance_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]


/-- Born-rule version of the acceptance-amplitude estimate in Lemma 3.4,
for two explicit dilation output vectors. No scalar amplitude hypothesis is
assumed: the actual effect square root and tensor operator estimate supply it. -/
theorem acceptance_amplitudes_of_vectors {b eN eM : ℕ} (T : Effect b)
    (C : Matrix (Fin eN) (Fin eM) ℂ)
    (x : EuclideanSpace ℂ (Fin b × Fin eN))
    (y : EuclideanSpace ℂ (Fin b × Fin eM)) (error : ℝ)
    (herror : ‖x - TensorNorm.matrixMap ((1 : Operator b) ⊗ₖ C) y‖ ≤ error) :
    Real.sqrt (dilationAcceptance T x) ≤
      ‖C‖ * Real.sqrt (dilationAcceptance T y) + error := by
  rw [sqrt_dilationAcceptance, sqrt_dilationAcceptance]
  exact TensorNorm.tensor_amplitude_le T.sqrtMatrix C x y error
    T.norm_sqrtMatrix_le_one herror

/-- Pure-input matrix form of Lemma 3.4, uniform over the Euclidean unit ball.
The output coordinate may already represent the joint reference-output system.
The separate reference extension/reassociation and mixed-input purification
bridges are not asserted by this declaration. -/
theorem acceptance_amplitudes_of_dilations {a b eN eM : ℕ} (T : Effect b)
    (C : Matrix (Fin eN) (Fin eM) ℂ)
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ)
    (ψ : EuclideanSpace ℂ (Fin a)) (hψ : ‖ψ‖ ≤ 1) :
    Real.sqrt (dilationAcceptance T (TensorNorm.matrixMap VN ψ)) ≤
      ‖C‖ * Real.sqrt (dilationAcceptance T (TensorNorm.matrixMap VM ψ)) +
        ‖VN - ((1 : Operator b) ⊗ₖ C) * VM‖ := by
  rw [sqrt_dilationAcceptance, sqrt_dilationAcceptance]
  exact TensorNorm.tensor_amplitude_le_of_operator_approx T.sqrtMatrix C VN VM ψ _
    T.norm_sqrtMatrix_le_one hψ le_rfl

end QuantumChannelStein



