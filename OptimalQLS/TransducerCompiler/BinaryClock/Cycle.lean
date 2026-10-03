import OptimalQLS.TransducerCompiler.BinaryClock.Counts

/-! # A complete linear-cost cached-comparator cycle with clean ancillas -/

namespace OptimalQLS.TransducerCompiler.BinaryClock
variable {ℓ : ℕ}

/-- Every counter mask acts correctly on arbitrary encoded clock strings, not just the counter. -/
theorem incrementProgram_run_general (ℓ t : ℕ) (x : Bits ℓ) :
    run (incrementProgram ℓ t) (encode x) =
      encode (fun i => Bool.xor (x i) (incrementMask ℓ t i)) :=
  updatePrefix_supported _ _ _ _ (incrementMask_supported ℓ t)

/-- A literal concatenation of the first `t` counter-update programs. -/
def counterPrefix (ℓ : ℕ) : ℕ → Program (Wire ℓ)
  | 0 => []
  | t + 1 => counterPrefix ℓ t ++ incrementProgram ℓ t

/-- Successive masks telescope, maintaining a valid comparator for every basis string. -/
theorem counterPrefix_run (t : ℕ) (x : Bits ℓ) :
    run (counterPrefix ℓ t) (encode x) =
      encode (fun i => Bool.xor (x i) (natBits ℓ t i)) := by
  induction t with
  | zero => simp [counterPrefix, natBits]
  | succ t ih =>
    rw [counterPrefix, run_append, ih, incrementProgram_run_general]
    congr 1
    funext i
    simp [incrementMask, Bool.xor_assoc]

theorem counterPrefix_length (ℓ t : ℕ) :
    (counterPrefix ℓ t).length =
      ∑ u ∈ Finset.range t, (incrementProgram ℓ u).length := by
  induction t with
  | zero => simp [counterPrefix]
  | succ t ih => simp [counterPrefix, List.length_append, Finset.sum_range_succ, ih]

/-- A complete binary cycle returns all clock bits to their starting values. -/
theorem counterPrefix_full_run (x : Bits ℓ) :
    run (counterPrefix ℓ (2 ^ ℓ)) (encode x) = encode x := by
  rw [counterPrefix_run]
  have hz : natBits ℓ (2 ^ ℓ) = fun _ => false := by
    calc
      natBits ℓ (2 ^ ℓ) = natBits ℓ (2 ^ ℓ % 2 ^ ℓ) := (natBits_mod ℓ _).symm
      _ = fun _ => false := by
        simp only [Nat.mod_self]
        funext i
        simp [natBits]
  simp [hz]

/-- Initialize the comparator, execute one complete cycle, and uncompute the comparator. -/
def cleanCycle (ℓ : ℕ) : Program (Wire ℓ) :=
  computePrefix ℓ le_rfl ++ counterPrefix ℓ (2 ^ ℓ) ++ (computePrefix ℓ le_rfl).reverse

/-- Exact cleanup on every computational-basis clock input. -/
theorem cleanCycle_run (x : Bits ℓ) : run (cleanCycle ℓ) (clean x) = clean x := by
  simp only [cleanCycle, run_append, compute_clean, counterPrefix_full_run, uncompute_clean]

theorem cleanCycle_length (ℓ : ℕ) : (cleanCycle ℓ).length ≤ 6 * ℓ + 14 * 2 ^ ℓ := by
  simp only [cleanCycle, List.length_append, List.length_reverse, counterPrefix_length]
  have hc := computePrefix_length ℓ (show ℓ ≤ ℓ from le_rfl)
  have hi := sum_incrementProgram_length ℓ
  omega

private theorem width_le_power (ℓ : ℕ) : ℓ ≤ 2 ^ ℓ := by
  induction ℓ with
  | zero => norm_num
  | succ ℓ ih =>
    rw [pow_succ]
    have hp : 0 < 2 ^ ℓ := by positivity
    omega

/-- Fully explicit linear primitive-gate bound including initialization and exact cleanup. -/
theorem cleanCycle_length_linear (ℓ : ℕ) : (cleanCycle ℓ).length ≤ 20 * 2 ^ ℓ := by
  have hc := cleanCycle_length ℓ
  have hw := width_le_power ℓ
  omega

end OptimalQLS.TransducerCompiler.BinaryClock
