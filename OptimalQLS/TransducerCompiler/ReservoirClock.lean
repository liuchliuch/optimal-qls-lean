import OptimalQLS.TransducerCompiler.LabelClock
import OptimalQLS.TransducerCompiler.Reservoir

/-! # Linear-cost label-dependent reservoir clock updates -/

namespace OptimalQLS.TransducerCompiler.BinaryClock

/-- Two physical label bits encode the four canonical transducer sectors. -/
def labelCode : Label → LabelBits
  | .pub => (false,false)
  | .internal => (false,true)
  | .first => (true,false)
  | .second => (true,true)

def truncMask (ℓ d t : ℕ) : Bits ℓ := fun i =>
  if i.val < d then incrementMask ℓ t i else false

theorem truncMask_supported (ℓ d t : ℕ) :
    ∀ i : Fin ℓ, carryWidth ℓ t ≤ i.val → truncMask ℓ d t i = false := by
  intro i hi
  simp [truncMask, incrementMask_supported ℓ t i hi]

/-- The truncation is exactly the XOR difference of the two actual modulo-clock addresses. -/
theorem truncMask_eq_addresses (ℓ d t : ℕ) (i : Fin ℓ) :
    truncMask ℓ d t i = Bool.xor (natBits ℓ (t % 2^d) i)
      (natBits ℓ ((t+1) % 2^d) i) := by
  by_cases hi : i.val < d <;>
    simp [truncMask, incrementMask, natBits, Nat.testBit_mod_two_pow, hi]

def trackWidth (ℓ d₁ d₂ : ℕ) : Label → ℕ
  | .pub => ℓ
  | .internal => 0
  | .first => d₁
  | .second => d₂

/-- Three independently selected low-bit updates; the internal track is fixed at zero. -/
def reservoirUpdate (ℓ d₁ d₂ t : ℕ) : Program (LabelWire ℓ) :=
  labelUpdate (labelCode .pub) (carryWidth ℓ t) (carryWidth_le ℓ t) (truncMask ℓ ℓ t) ++
  labelUpdate (labelCode .first) (carryWidth ℓ t) (carryWidth_le ℓ t) (truncMask ℓ d₁ t) ++
  labelUpdate (labelCode .second) (carryWidth ℓ t) (carryWidth_le ℓ t) (truncMask ℓ d₂ t)

/-- The complete selected-label update preserves the exact comparator encoding. -/
theorem reservoirUpdate_run (ℓ d₁ d₂ t : ℕ) (l : Label) (x : Bits ℓ) :
    run (reservoirUpdate ℓ d₁ d₂ t) (extend (labelCode l) (encode x)) =
      extend (labelCode l) (encode (xorLow (carryWidth ℓ t) x
        (truncMask ℓ (trackWidth ℓ d₁ d₂ l) t))) := by
  cases l <;> simp [reservoirUpdate, run_append, labelUpdate_run, labelCode, trackWidth,
    truncMask, xorLow]
  congr 2
  funext i
  simp [xorLow, truncMask]

/-- Exact address-difference semantics on every label and every clock basis state. -/
theorem reservoirUpdate_supported (ℓ d₁ d₂ t : ℕ) (l : Label) (x : Bits ℓ) :
    run (reservoirUpdate ℓ d₁ d₂ t) (extend (labelCode l) (encode x)) =
      extend (labelCode l) (encode (fun i => Bool.xor (x i)
        (truncMask ℓ (trackWidth ℓ d₁ d₂ l) t i))) := by
  rw [reservoirUpdate_run]
  congr 2
  funext i
  by_cases hi : i.val < carryWidth ℓ t
  · simp [xorLow, hi]
  · simp [xorLow, hi, truncMask_supported ℓ (trackWidth ℓ d₁ d₂ l) t i (by omega)]

theorem reservoirUpdate_length (ℓ d₁ d₂ t : ℕ) :
    (reservoirUpdate ℓ d₁ d₂ t).length ≤ 33 * carryWidth ℓ t := by
  simp only [reservoirUpdate, List.length_append]
  have h₀ := labelUpdate_length (labelCode .pub) (carryWidth ℓ t)
    (carryWidth_le ℓ t) (truncMask ℓ ℓ t)
  have h₁ := labelUpdate_length (labelCode .first) (carryWidth ℓ t)
    (carryWidth_le ℓ t) (truncMask ℓ d₁ t)
  have h₂ := labelUpdate_length (labelCode .second) (carryWidth ℓ t)
    (carryWidth_le ℓ t) (truncMask ℓ d₂ t)
  omega

/-- All K reservoir-frame updates cost at most 66K literal reversible primitives. -/
theorem sum_reservoirUpdate_length (ℓ d₁ d₂ : ℕ) :
    (∑ t ∈ Finset.range (2^ℓ), (reservoirUpdate ℓ d₁ d₂ t).length) ≤ 66 * 2^ℓ := by
  calc
    _ ≤ ∑ t ∈ Finset.range (2^ℓ), 33 * carryWidth ℓ t :=
      Finset.sum_le_sum (fun t _ => reservoirUpdate_length ℓ d₁ d₂ t)
    _ = 33 * (∑ t ∈ Finset.range (2^ℓ), carryWidth ℓ t) := by rw [Finset.mul_sum]
    _ ≤ 66 * 2^ℓ := by have h := sum_carryWidth_le ℓ; omega

end OptimalQLS.TransducerCompiler.BinaryClock
