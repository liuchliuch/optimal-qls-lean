import OptimalQLS.TransducerCompiler.BinaryClock.Comparator

/-! # Clean low-bit updates of the cached binary comparator -/

namespace OptimalQLS.TransducerCompiler.BinaryClock
variable {ℓ : ℕ}

/-- XOR a chosen mask into just the `r` lowest clock positions. -/
def xorLow (r : ℕ) (x mask : Bits ℓ) : Bits ℓ :=
  fun i => Bool.xor (x i) (if i.val < r then mask i else false)

/-- The same change on clock wires, leaving every ancilla untouched. -/
def flipState (r : ℕ) (mask : Bits ℓ) (b : State ℓ) : State ℓ
  | .inl i => Bool.xor (b (.inl i)) (if i.val < r then mask i else false)
  | .inr i => b (.inr i)

/-- A literal list of NOT gates for the supported mask positions. -/
def flipPrefix : (r : ℕ) → r ≤ ℓ → Bits ℓ → Program (Wire ℓ)
  | 0, _, _ => []
  | r + 1, hr, mask => flipPrefix r (by omega) mask ++
      (if mask ⟨r, by omega⟩ then [.x (.inl ⟨r, by omega⟩)] else [])

private theorem flipNext_run (r : ℕ) (hr : r < ℓ) (mask : Bits ℓ) (b : State ℓ) :
    run (if mask ⟨r, hr⟩ then [.x (.inl ⟨r, hr⟩)] else []) (flipState r mask b) =
      flipState (r + 1) mask b := by
  funext w
  cases w with
  | inl j =>
    by_cases hj : j = (⟨r, hr⟩ : Fin ℓ)
    · subst j
      cases hm : mask ⟨r, hr⟩ <;>
        simp [hm, run, Gate.act, Function.update_apply, flipState]
    · have hv : j.val ≠ r := fun he => hj (Fin.ext he)
      have hlt : j.val < r + 1 ↔ j.val < r := by omega
      cases hm : mask ⟨r, hr⟩ <;>
        simp [hm, run, Gate.act, Function.update_apply, flipState, hj, hlt]
  | inr j =>
    cases hm : mask ⟨r, hr⟩ <;> simp [hm, run, Gate.act, Function.update_apply, flipState]

theorem flipPrefix_run (r : ℕ) (hr : r ≤ ℓ) (mask : Bits ℓ) (b : State ℓ) :
    run (flipPrefix r hr mask) b = flipState r mask b := by
  induction r with
  | zero =>
    funext w
    cases w <;> simp [flipPrefix, run, flipState]
  | succ r ih =>
    rw [flipPrefix, run_append, ih]
    exact flipNext_run r (by omega) mask b

theorem flipPrefix_length (r : ℕ) (hr : r ≤ ℓ) (mask : Bits ℓ) :
    (flipPrefix r hr mask).length ≤ r := by
  induction r with
  | zero => simp [flipPrefix]
  | succ r ih =>
    rw [flipPrefix, List.length_append]
    have hl := ih (by omega)
    split <;> simp only [List.length_cons, List.length_nil] <;> omega

/-- The retained high comparator bits remain valid after a supported low-bit change. -/
theorem flipPrefix_partial (r : ℕ) (hr : r ≤ ℓ) (mask x : Bits ℓ) :
    run (flipPrefix r hr mask) (partialEncode r x) = partialEncode r (xorLow r x mask) := by
  rw [flipPrefix_run]
  funext w
  cases w with
  | inl i => rfl
  | inr i =>
    change (if i.val < r then false else suffixZero x i.val) =
      if i.val < r then false else suffixZero (xorLow r x mask) i.val
    split_ifs with hi
    · rfl
    · apply suffixZero_congr
      intro j hj
      have hn : ¬ j.val < r := by omega
      simp [xorLow, hn]

/-- Uncompute only the affected low comparator bits, flip the clock, then recompute. -/
def updatePrefix (r : ℕ) (hr : r ≤ ℓ) (mask : Bits ℓ) : Program (Wire ℓ) :=
  (computePrefix r hr).reverse ++ flipPrefix r hr mask ++ computePrefix r hr

/-- Exact semantics of the real reversible update on every valid encoded basis state. -/
theorem updatePrefix_run (r : ℕ) (hr : r ≤ ℓ) (mask x : Bits ℓ) :
    run (updatePrefix r hr mask) (encode x) = encode (xorLow r x mask) := by
  simp only [updatePrefix, run_append, uncomputePrefix_run, flipPrefix_partial, computePrefix_run]

/-- Each changed low position costs at most seven NOT/CNOT/Toffoli primitives. -/
theorem updatePrefix_length (r : ℕ) (hr : r ≤ ℓ) (mask : Bits ℓ) :
    (updatePrefix r hr mask).length ≤ 7 * r := by
  simp only [updatePrefix, List.length_append, List.length_reverse]
  have hc := computePrefix_length r hr
  have hf := flipPrefix_length r hr mask
  omega

/-- When the supplied mask is already supported below `r`, the update applies that exact mask. -/
theorem updatePrefix_supported (r : ℕ) (hr : r ≤ ℓ) (mask x : Bits ℓ)
    (hmask : ∀ i : Fin ℓ, r ≤ i.val → mask i = false) :
    run (updatePrefix r hr mask) (encode x) = encode (fun i => Bool.xor (x i) (mask i)) := by
  rw [updatePrefix_run]
  congr 1
  funext i
  by_cases hi : i.val < r
  · simp [xorLow, hi]
  · simp [xorLow, hi, hmask i (by omega)]

end OptimalQLS.TransducerCompiler.BinaryClock
