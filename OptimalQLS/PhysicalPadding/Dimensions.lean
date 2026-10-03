import OptimalQLS.PhysicalPadding.Operators
import OptimalQLS.PhysicalPadding.Registers
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Exact logarithmic padding size and the necessary singularity boundary. -/
noncomputable section
namespace OptimalQLS.PhysicalPadding
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- The natural ceiling agrees literally with the paper's ceiling base-two log. -/
theorem dataQubits_eq_ceil_log (d : ℕ) :
    dataQubits d = ⌈Real.log (d : ℝ) / Real.log 2⌉₊ := by
  simpa [dataQubits, Real.logb] using (Real.natCeil_logb_natCast 2 d).symm

theorem physicalDimension_eq_paper (d : ℕ) :
    physicalDimension d = 2 ^ ⌈Real.log (d : ℝ) / Real.log 2⌉₊ := by
  rw [physicalDimension, dataQubits_eq_ceil_log]

/-- The data qubit count is minimal among all covering binary registers. -/
theorem dataQubits_le_iff (d n : ℕ) : dataQubits d ≤ n ↔ d ≤ 2^n :=
  Nat.clog_le_iff_le_pow (by decide)

@[simp] theorem dataQubits_power_two (n : ℕ) : dataQubits (2^n) = n :=
  Nat.clog_pow 2 n (by decide)

@[simp] theorem physicalDimension_power_two (n : ℕ) : physicalDimension (2^n) = 2^n := by
  simp [physicalDimension]

/-- Any genuinely unused computational coordinate lies in the physical kernel.
Consequently the full zero-extended matrix cannot be assumed invertible. -/
theorem zeroExtend_not_isUnit {D P : Type*} [Fintype D] [DecidableEq D]
    [Fintype P] [DecidableEq P] (f : D ↪ P) (A : Matrix D D ℂ)
    (p : P) (hp : p ∉ Set.range f) : ¬ IsUnit (zeroExtend f A) := by
  intro hU
  have h := congrArg (fun M : Matrix P P ℂ => M p p)
    (Ring.inverse_mul_cancel (zeroExtend f A) hU)
  have hz (q : P) : zeroExtend f A q p = 0 := zeroExtend_inactive_column f A q p hp
  simp [Matrix.mul_apply, hz] at h

theorem physicalMatrix_not_isUnit {d : ℕ} (hpad : d < physicalDimension d)
    (A : Matrix (Fin d) (Fin d) ℂ) : ¬ IsUnit (physicalMatrix A) := by
  let p : Fin (physicalDimension d) := ⟨d,hpad⟩
  apply zeroExtend_not_isUnit (activeIndex d) A p
  rintro ⟨i,hi⟩
  have hh := congrArg Fin.val hi
  have hil := i.isLt
  change i.val = d at hh
  omega

end OptimalQLS.PhysicalPadding
