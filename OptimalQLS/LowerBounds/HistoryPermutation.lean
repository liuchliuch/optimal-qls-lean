import OptimalQLS.LowerBounds.Parity
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Group.Conj

/-!
# Explicit clock/work permutations for cyclic computation histories

The work register is an actual Boolean bit. A clock-dependent reversible
X-gauge conjugates a cyclic shift into the computation-history transition.
The matrix uses the forward permutation convention (column basis vectors move
forward); this matters because mathlib's raw `permMatrix` uses the transpose
convention.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Fin.NatCast
namespace OptimalQLS.LowerBounds

abbrev HistoryBasis (N : ℕ) := Fin N × Bool

def clockShift (N : ℕ) [NeZero N] : Equiv.Perm (HistoryBasis N) :=
  (finCycle (1 : Fin N)).prodCongr (Equiv.refl Bool)

@[simp] theorem clockShift_apply {N : ℕ} [NeZero N] (j : Fin N) (b : Bool) :
    clockShift N (j, b) = (j + 1, b) := rfl

@[simp] theorem clockShift_pow_apply {N : ℕ} [NeZero N] (k : ℕ)
    (j : Fin N) (b : Bool) :
    (clockShift N ^ k) (j, b) = (j + (k : Fin N), b) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, clockShift_apply]
    simp [Nat.cast_add, add_assoc]

@[simp] theorem clockShift_pow_length (N : ℕ) [NeZero N] :
    clockShift N ^ N = 1 := by
  apply Equiv.ext
  rintro ⟨j, b⟩
  simp

def gaugeMap {N : ℕ} (profile : Fin N → Bool) (b : HistoryBasis N) : HistoryBasis N :=
  (b.1, Bool.xor b.2 (profile b.1))

@[simp] theorem gaugeMap_involutive {N : ℕ} (profile : Fin N → Bool) :
    Function.Involutive (gaugeMap profile) := by
  rintro ⟨j, b⟩
  cases b <;> cases h : profile j <;> simp [gaugeMap, h]

def historyGauge {N : ℕ} (profile : Fin N → Bool) : Equiv.Perm (HistoryBasis N) :=
  (gaugeMap_involutive profile).toPerm

@[simp] theorem historyGauge_apply {N : ℕ} (profile : Fin N → Bool) (b : HistoryBasis N) :
    historyGauge profile b = gaugeMap profile b := rfl

@[simp] theorem historyGauge_inv {N : ℕ} (profile : Fin N → Bool) :
    (historyGauge profile)⁻¹ = historyGauge profile := rfl

/-- Explicit gauge-conjugated forward transition. -/
def historyPermutation {N : ℕ} [NeZero N] (profile : Fin N → Bool) :
    Equiv.Perm (HistoryBasis N) :=
  historyGauge profile * clockShift N * (historyGauge profile)⁻¹

/-- The gate at clock `j` is exactly `X^(profile j XOR profile (j+1))`. -/
theorem historyPermutation_apply {N : ℕ} [NeZero N] (profile : Fin N → Bool)
    (j : Fin N) (b : Bool) :
    historyPermutation profile (j, b) =
      (j + 1, Bool.xor b (Bool.xor (profile j) (profile (j + 1)))) := by
  simp [historyPermutation, Equiv.Perm.mul_apply, historyGauge, gaugeMap, clockShift,
    Bool.xor_assoc]

theorem historyPermutation_pow_length {N : ℕ} [NeZero N] (profile : Fin N → Bool) :
    historyPermutation profile ^ N = 1 := by
  rw [historyPermutation, conj_pow, clockShift_pow_length, mul_one, mul_inv_cancel]

/-- Matrix of the actual forward permutation, mapping `|j,b>` to the next
clock with the appropriate X-gate. -/
def historyStep {N : ℕ} [NeZero N] (profile : Fin N → Bool) :
    Matrix (HistoryBasis N) (HistoryBasis N) ℂ :=
  Matrix.permMatrixHom (R := ℂ) (historyPermutation profile)

/-- No history-period premise is assumed: the exact period follows from the
concrete clock permutation and gauge construction. -/
theorem historyStep_pow_length {N : ℕ} [NeZero N] (profile : Fin N → Bool) :
    historyStep profile ^ N = 1 := by
  rw [historyStep, ← map_pow, historyPermutation_pow_length, map_one]

theorem historyStep_unitary {N : ℕ} [NeZero N] (profile : Fin N → Bool) :
    (historyStep profile).conjTranspose * historyStep profile = 1 := by
  simp [historyStep, Matrix.permMatrixHom, ← Matrix.permMatrix_mul]

theorem historyStep_norm {N : ℕ} [NeZero N] (profile : Fin N → Bool) :
    ‖historyStep profile‖ = 1 := by
  exact Matrix.permMatrix_l2_opNorm_eq _

end OptimalQLS.LowerBounds
