import OptimalQLS.LowerBounds.HistoryPermutation
import Mathlib.Data.List.TakeDrop

/-!
# The literal reversible parity transition list

The first and last padding, forward input traversal, parity interval, and
reverse uncomputation are the sequence in Definition 6.2. Prefix XOR is the
clock-dependent X-gauge. All list lengths and parity-storage claims below are
proved for the concrete sequence, not postulated as circuit properties.
-/
namespace OptimalQLS.LowerBounds

def xorFold : List Bool → Bool
  | [] => false
  | b :: l => Bool.xor b (xorFold l)

@[simp] theorem xorFold_nil : xorFold [] = false := rfl
@[simp] theorem xorFold_singleton (b : Bool) : xorFold [b] = b := by simp [xorFold]

@[simp] theorem xorFold_append (a b : List Bool) :
    xorFold (a ++ b) = Bool.xor (xorFold a) (xorFold b) := by
  induction a with
  | nil => simp [xorFold]
  | cons a l ih => simp [xorFold, ih, Bool.xor_assoc]

@[simp] theorem xorFold_reverse (a : List Bool) : xorFold a.reverse = xorFold a := by
  induction a with
  | nil => rfl
  | cons b l ih => simp [List.reverse_cons, ih, xorFold, Bool.xor_comm]

@[simp] theorem xorFold_replicate_false (k : ℕ) : xorFold (List.replicate k false) = false := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, xorFold, ih]

/-- The exact gate sequence, with `false` denoting I and `true` denoting X. -/
def parityHistoryGates (ell : ℕ) (z : List Bool) : List Bool :=
  ((List.replicate (ell - 1) false ++ z) ++ List.replicate ell false) ++
    (z.reverse ++ [false])

@[simp] theorem parityHistoryGates_length {ell : ℕ} (hell : 1 ≤ ell) (z : List Bool) :
    (parityHistoryGates ell z).length = 2 * ell + 2 * z.length := by
  simp [parityHistoryGates]
  omega

/-- Reversible uncomputation closes the work register exactly around the cycle. -/
@[simp] theorem parityHistoryGates_xor (ell : ℕ) (z : List Bool) :
    xorFold (parityHistoryGates ell z) = false := by
  simp [parityHistoryGates]

theorem take_length_add_append {α : Type*} (a b : List α) (k : ℕ) :
    (a ++ b).take (a.length + k) = a ++ b.take k := by
  rw [List.take_append, List.take_of_length_le (by omega)]
  simp

/-- The first `ell` clock states have work bit zero, as needed for the source
state's exact invariance under the gauge. -/
theorem parityHistoryGates_initial_prefix {ell j : ℕ} (z : List Bool)
    (hj : j < ell) :
    xorFold ((parityHistoryGates ell z).take j) = false := by
  have hj' : j ≤ (List.replicate (ell - 1) false).length := by simp; omega
  have heq : parityHistoryGates ell z = List.replicate (ell - 1) false ++
      (z ++ List.replicate ell false ++ z.reverse ++ [false]) := by
    simp [parityHistoryGates, List.append_assoc]
  rw [heq, List.take_append_of_le_length hj']
  simp [List.take_replicate]

/-- The entire middle padding interval stores the parity of the input. -/
theorem parityHistoryGates_tail_prefix {ell k : ℕ} (z : List Bool)
    (hk : k ≤ ell) :
    xorFold ((parityHistoryGates ell z).take (ell - 1 + z.length + k)) = xorFold z := by
  have heq : parityHistoryGates ell z =
      (List.replicate (ell - 1) false ++ z) ++
      (List.replicate ell false ++ (z.reverse ++ [false])) := by
    simp [parityHistoryGates, List.append_assoc]
  have hlen : (List.replicate (ell - 1) false ++ z).length = ell - 1 + z.length := by simp
  rw [heq, ← hlen, take_length_add_append,
    List.take_append_of_le_length (by simpa using hk)]
  simp [List.take_replicate]

/-- The input-dependent profile for a clock of exactly the transition length. -/
def parityHistoryProfile (ell : ℕ) (z : List Bool) :
    Fin (parityHistoryGates ell z).length → Bool :=
  fun j => xorFold ((parityHistoryGates ell z).take j.val)

/-- Consecutive prefix gauges recover the literal transition gate. -/
theorem xorFold_take_step (gates : List Bool) (j : Fin gates.length) :
    Bool.xor (xorFold (gates.take j.val)) (xorFold (gates.take (j.val + 1))) = gates[j.val] := by
  rw [List.take_succ_eq_append_getElem j.isLt, xorFold_append, xorFold_singleton]
  cases xorFold (gates.take j.val) <;> cases gates[j.val] <;> rfl

end OptimalQLS.LowerBounds
