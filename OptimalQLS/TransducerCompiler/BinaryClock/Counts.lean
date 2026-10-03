import OptimalQLS.TransducerCompiler.BinaryClock.Update

/-! # Binary-increment semantics and amortized primitive-gate counts -/

namespace OptimalQLS.TransducerCompiler.BinaryClock

/-- Bounded trailing-ones length plus one, with wraparound capped at the register width. -/
def carryWidth : ℕ → ℕ → ℕ
  | 0, _ => 0
  | ℓ + 1, t => if t % 2 = 0 then 1 else 1 + carryWidth ℓ (t / 2)

theorem carryWidth_le (ℓ t : ℕ) : carryWidth ℓ t ≤ ℓ := by
  induction ℓ generalizing t with
  | zero => simp [carryWidth]
  | succ ℓ ih =>
    simp only [carryWidth]
    split
    · omega
    · have h := ih (t / 2)
      omega

@[simp] theorem carryWidth_even (ℓ t : ℕ) : carryWidth (ℓ + 1) (2 * t) = 1 := by
  simp [carryWidth]

@[simp] theorem carryWidth_odd (ℓ t : ℕ) :
    carryWidth (ℓ + 1) (2 * t + 1) = 1 + carryWidth ℓ t := by
  simp [carryWidth, Nat.add_mod, Nat.mul_mod, Nat.add_div]

/-- Every bit above the carry width is unchanged by the actual binary increment. -/
theorem carryWidth_stable (ℓ t i : ℕ) (hi : i < ℓ) (hwidth : carryWidth ℓ t ≤ i) :
    Nat.testBit (t + 1) i = Nat.testBit t i := by
  induction ℓ generalizing t i with
  | zero => omega
  | succ ℓ ih =>
    cases i with
    | zero =>
      simp only [carryWidth] at hwidth
      split at hwidth <;> omega
    | succ i =>
      rw [Nat.testBit_succ, Nat.testBit_succ]
      by_cases he : t % 2 = 0
      · have hd : (t + 1) / 2 = t / 2 := by omega
        rw [hd]
      · have hd : (t + 1) / 2 = t / 2 + 1 := by omega
        rw [hd]
        apply ih (t / 2) i (by omega)
        simp only [carryWidth, he, if_false] at hwidth
        omega

private theorem sum_range_double (f : ℕ → ℕ) (N : ℕ) :
    (∑ t ∈ Finset.range (2 * N), f t) =
      ∑ t ∈ Finset.range N, (f (2 * t) + f (2 * t + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp [Nat.mul_succ, Finset.sum_range_succ, ih]
    omega

/-- Exact binary-counter amortization: the full cycle changes `2K-2` bit positions. -/
theorem sum_carryWidth (ℓ : ℕ) :
    (∑ t ∈ Finset.range (2 ^ ℓ), carryWidth ℓ t) + 2 = 2 * 2 ^ ℓ := by
  induction ℓ with
  | zero => simp [carryWidth]
  | succ ℓ ih =>
    rw [pow_succ, Nat.mul_comm (2 ^ ℓ) 2, sum_range_double]
    simp only [carryWidth_even, carryWidth_odd, ← Nat.add_assoc,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
    omega

theorem sum_carryWidth_le (ℓ : ℕ) :
    (∑ t ∈ Finset.range (2 ^ ℓ), carryWidth ℓ t) ≤ 2 * 2 ^ ℓ := by
  have h := sum_carryWidth ℓ
  omega

/-- Standard low-first binary encoding of a natural number in a fixed-width register. -/
def natBits (ℓ t : ℕ) : Bits ℓ := fun i => Nat.testBit t i.val

/-- The actual bit difference of successive counter values. -/
def incrementMask (ℓ t : ℕ) : Bits ℓ :=
  fun i => Bool.xor (natBits ℓ t i) (natBits ℓ (t + 1) i)

theorem incrementMask_supported (ℓ t : ℕ) :
    ∀ i : Fin ℓ, carryWidth ℓ t ≤ i.val → incrementMask ℓ t i = false := by
  intro i hi
  simp only [incrementMask, natBits, carryWidth_stable ℓ t i.val i.isLt hi, Bool.xor_self]

/-- The concrete low-bit update for the next value of the binary counter. -/
def incrementProgram (ℓ t : ℕ) : Program (Wire ℓ) :=
  updatePrefix (carryWidth ℓ t) (carryWidth_le ℓ t) (incrementMask ℓ t)

theorem incrementProgram_run (ℓ t : ℕ) :
    run (incrementProgram ℓ t) (encode (natBits ℓ t)) = encode (natBits ℓ (t + 1)) := by
  rw [incrementProgram, updatePrefix_supported _ _ _ _ (incrementMask_supported ℓ t)]
  congr 1
  funext i
  simp [incrementMask]

/-- The binary increment is cyclic on the finite clock register. -/
theorem natBits_mod (ℓ t : ℕ) : natBits ℓ (t % 2 ^ ℓ) = natBits ℓ t := by
  funext i
  simp [natBits, Nat.testBit_mod_two_pow, i.isLt]

theorem incrementProgram_run_mod (ℓ t : ℕ) :
    run (incrementProgram ℓ t) (encode (natBits ℓ t)) =
      encode (natBits ℓ ((t + 1) % 2 ^ ℓ)) := by
  rw [natBits_mod, incrementProgram_run]

/-- Amortized linear total cost for all cached-comparator increments. -/
theorem sum_incrementProgram_length (ℓ : ℕ) :
    (∑ t ∈ Finset.range (2 ^ ℓ), (incrementProgram ℓ t).length) ≤ 14 * 2 ^ ℓ := by
  calc
    _ ≤ ∑ t ∈ Finset.range (2 ^ ℓ), 7 * carryWidth ℓ t := by
      apply Finset.sum_le_sum
      intro t ht
      exact updatePrefix_length _ _ _
    _ = 7 * ∑ t ∈ Finset.range (2 ^ ℓ), carryWidth ℓ t := by rw [Finset.mul_sum]
    _ ≤ 14 * 2 ^ ℓ := by have h := sum_carryWidth_le ℓ; omega

end OptimalQLS.TransducerCompiler.BinaryClock
