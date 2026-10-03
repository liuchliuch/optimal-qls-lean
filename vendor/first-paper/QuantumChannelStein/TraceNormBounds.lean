import QuantumChannelStein.TraceNorm
import QuantumChannelStein.ReferenceAcceptance

/-! # Standard trace-norm bounds for actual dilation matrices -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.TraceNorm
open Matrix
open scoped BigOperators Kronecker Matrix.Norms.L2Operator
variable {n m e : Type*} [Fintype n] [Fintype m] [Fintype e]
  [DecidableEq n] [DecidableEq m] [DecidableEq e]

/-- The genuine trace-square-root norm satisfies the rectangular sandwich bound. -/
theorem traceNorm_sandwich_le (A : Matrix m n ℂ) (X : Matrix n n ℂ) (B : Matrix n m ℂ) :
    traceNorm (A * X * B) ≤ ‖A‖ * traceNorm X * ‖B‖ := by
  obtain ⟨U, hU⟩ := exists_unitary_trace_eq (A * X * B)
  have hcycle : ((U : Matrix m m ℂ) * (A * X * B)).trace =
      ((B * (U : Matrix m m ℂ) * A) * X).trace := by
    rw [show (U : Matrix m m ℂ) * (A * X * B) = ((U : Matrix m m ℂ) * A * X) * B by simp [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hnorm : ‖B * (U : Matrix m m ℂ) * A‖ ≤ ‖B‖ * ‖A‖ := by
    calc
      _ ≤ ‖B * (U : Matrix m m ℂ)‖ * ‖A‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖B‖ * ‖(U : Matrix m m ℂ)‖) * ‖A‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ ≤ (‖B‖ * 1) * ‖A‖ := by gcongr; exact unitary_opNorm_le_one U
      _ = ‖B‖ * ‖A‖ := by ring
  calc
    _ = ((B * (U : Matrix m m ℂ) * A) * X).trace.re := by rw [← hU, hcycle]
    _ ≤ ‖((B * (U : Matrix m m ℂ) * A) * X).trace‖ := Complex.re_le_norm _
    _ ≤ ‖B * (U : Matrix m m ℂ) * A‖ * traceNorm X := norm_trace_mul_le _ _
    _ ≤ (‖B‖ * ‖A‖) * traceNorm X :=
      mul_le_mul_of_nonneg_right hnorm (traceNorm_nonneg X)
    _ = ‖A‖ * traceNorm X * ‖B‖ := by ring

/-- The partial trace is contractive for the standard trace norm on all
matrices; Hermitian inputs are a special case, not an assumed interface. -/
theorem traceNorm_partialTrace_le (X : Matrix (m × e) (m × e) ℂ) :
    traceNorm (ReferenceAcceptance.traceEnvironment X) ≤ traceNorm X := by
  obtain ⟨U, hU⟩ := exists_unitary_trace_eq (ReferenceAcceptance.traceEnvironment X)
  rw [← hU, ReferenceAcceptance.traceEnvironment_duality]
  exact (Complex.re_le_norm _).trans ((norm_trace_mul_le _ _).trans
    (mul_le_of_le_one_left (traceNorm_nonneg X)
      ((TensorNorm.kronecker_one_opNorm_le (U : Matrix m m ℂ)).trans (unitary_opNorm_le_one U))))

/-- The trace-norm difference of conjugation outputs is controlled by the
actual dilation operator error, for every matrix input. -/
theorem traceNorm_dilation_difference_le
    (V W : Matrix m n ℂ) (X : Matrix n n ℂ) :
    traceNorm (V * X * Vᴴ - W * X * Wᴴ) ≤
      (‖V‖ + ‖W‖) * ‖V - W‖ * traceNorm X := by
  have hsplit : V * X * Vᴴ - W * X * Wᴴ =
      (V - W) * X * Vᴴ + W * X * (V - W)ᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [hsplit]
  calc
    _ ≤ traceNorm ((V - W) * X * Vᴴ) + traceNorm (W * X * (V - W)ᴴ) := traceNorm_add_le _ _
    _ ≤ ‖V - W‖ * traceNorm X * ‖Vᴴ‖ + ‖W‖ * traceNorm X * ‖(V - W)ᴴ‖ :=
      add_le_add (traceNorm_sandwich_le _ _ _) (traceNorm_sandwich_le _ _ _)
    _ = _ := by simp only [Matrix.l2_opNorm_conjTranspose]; ring

end QuantumChannelStein.TraceNorm
