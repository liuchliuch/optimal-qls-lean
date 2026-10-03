import OptimalQLS.TransducerCompiler.BinaryClock.Gates

/-! # A clean reversible suffix-zero comparator for a binary clock -/

namespace OptimalQLS.TransducerCompiler.BinaryClock

abbrev Wire (ℓ : ℕ) := Fin ℓ ⊕ Fin ℓ
abbrev Bits (ℓ : ℕ) := Fin ℓ → Bool
abbrev State (ℓ : ℕ) := Wire ℓ → Bool

variable {ℓ : ℕ}

/-- Ancilla bit `i` indicates that every clock bit at position at least `i` is zero. -/
def suffixZero (x : Bits ℓ) (i : ℕ) : Bool :=
  decide (∀ j : Fin ℓ, i ≤ j.val → x j = false)

theorem suffixZero_step (x : Bits ℓ) (i : Fin ℓ) :
    suffixZero x i.val = (!(x i) && suffixZero x (i.val + 1)) := by
  rw [Bool.eq_iff_iff]
  simp only [suffixZero, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false, decide_eq_true_eq]
  constructor
  · intro h
    refine ⟨h i le_rfl, ?_⟩
    intro j hj
    exact h j (by omega)
  · rintro ⟨hi, h⟩ j hj
    by_cases he : j = i
    · simpa [he] using hi
    · have hv : j.val ≠ i.val := fun hv => he (Fin.ext hv)
      exact h j (by omega)

theorem suffixZero_above (x : Bits ℓ) {i : ℕ} (hi : ℓ ≤ i) : suffixZero x i = true := by
  simp only [suffixZero, decide_eq_true_eq]
  intro j hj
  omega

theorem suffixZero_congr {x y : Bits ℓ} {i : ℕ}
    (h : ∀ j : Fin ℓ, i ≤ j.val → x j = y j) : suffixZero x i = suffixZero y i := by
  rw [Bool.eq_iff_iff]
  simp only [suffixZero, decide_eq_true_eq]
  constructor
  · intro hz j hj
    rw [← h j hj]
    exact hz j hj
  · intro hz j hj
    rw [h j hj]
    exact hz j hj

/-- A partly computed comparator, whose `r` lowest ancillas are still zero. -/
def partialEncode (r : ℕ) (x : Bits ℓ) : State ℓ
  | .inl i => x i
  | .inr i => if i.val < r then false else suffixZero x i.val

/-- The fully computed comparator register. -/
def encode (x : Bits ℓ) : State ℓ := partialEncode 0 x

/-- The input clock with all comparator ancillas clean. -/
def clean (x : Bits ℓ) : State ℓ
  | .inl i => x i
  | .inr _ => false

@[simp] theorem partialEncode_zero (x : Bits ℓ) : partialEncode 0 x = encode x := rfl
@[simp] theorem partialEncode_full (x : Bits ℓ) : partialEncode ℓ x = clean x := by
  funext w
  cases w with
  | inl i => rfl
  | inr i => simp [partialEncode, clean, i.isLt]

/-- The higher ancilla is a true sentinel at the top of the register. -/
def nextAnc (b : State ℓ) (i : Fin ℓ) : Bool :=
  if h : i.val + 1 < ℓ then b (.inr ⟨i.val + 1, h⟩) else true

/-- Compute one comparator bit with two or three literal primitive gates. -/
def writeBit (i : Fin ℓ) : Program (Wire ℓ) :=
  if h : i.val + 1 < ℓ then
    [.x (.inl i),
     .ccx (.inl i) (.inr ⟨i.val + 1, h⟩) (.inr i) (by simp)
       (by intro he; have he' := congrArg Fin.val (Sum.inr.inj he); simp at he'),
     .x (.inl i)]
  else [.x (.inr i), .cx (.inl i) (.inr i) (by simp)]

theorem writeBit_length (i : Fin ℓ) : (writeBit i).length ≤ 3 := by
  unfold writeBit
  split <;> simp

/-- The literal gates XOR the suffix predicate into exactly one ancilla bit. -/
theorem writeBit_run (i : Fin ℓ) (b : State ℓ) :
    run (writeBit i) b = Function.update b (.inr i)
      (Bool.xor (b (.inr i)) (!(b (.inl i)) && nextAnc b i)) := by
  funext w
  by_cases hn : i.val + 1 < ℓ
  · cases w with
    | inl j =>
      by_cases hj : j = i <;>
        simp [writeBit, hn, run, Gate.act, Function.update_apply, hj, nextAnc]
    | inr j =>
      by_cases hj : j = i <;>
        simp [writeBit, hn, run, Gate.act, Function.update_apply, hj, nextAnc]
  · cases w with
    | inl j => simp [writeBit, hn, run, Gate.act, Function.update_apply]
    | inr j =>
      by_cases hj : j = i
      · subst j
        cases hb : b (.inr i) <;> cases hc : b (.inl i) <;>
          simp [writeBit, hn, run, Gate.act, Function.update_apply, nextAnc, hb, hc]
      · simp [writeBit, hn, run, Gate.act, Function.update_apply, hj]

theorem nextAnc_partial (x : Bits ℓ) (i : Fin ℓ) :
    nextAnc (partialEncode (i.val + 1) x) i = suffixZero x (i.val + 1) := by
  by_cases hi : i.val + 1 < ℓ
  · simp [nextAnc, hi, partialEncode]
  · simp [nextAnc, hi, suffixZero_above x (by omega : ℓ ≤ i.val + 1)]

/-- Each concrete bit-writing program advances the valid comparator invariant. -/
theorem writeBit_partial (x : Bits ℓ) (i : Fin ℓ) :
    run (writeBit i) (partialEncode (i.val + 1) x) = partialEncode i.val x := by
  rw [writeBit_run]
  funext w
  cases w with
  | inl j => simp [Function.update_apply, partialEncode]
  | inr j =>
    by_cases hj : j = i
    · subst j
      simp [Function.update_apply, nextAnc_partial, partialEncode, suffixZero_step]
    · have hv : j.val ≠ i.val := fun he => hj (Fin.ext he)
      have hlt : j.val < i.val + 1 ↔ j.val < i.val := by omega
      simp [Function.update_apply, hj, partialEncode, hlt]

/-- Compute the lowest `r` comparator bits, in descending significance order. -/
def computePrefix : (r : ℕ) → r ≤ ℓ → Program (Wire ℓ)
  | 0, _ => []
  | r + 1, hr => writeBit ⟨r, by omega⟩ ++ computePrefix r (by omega)

theorem computePrefix_run (r : ℕ) (hr : r ≤ ℓ) (x : Bits ℓ) :
    run (computePrefix r hr) (partialEncode r x) = encode x := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [computePrefix, run_append, writeBit_partial]
    exact ih (by omega)

theorem computePrefix_length (r : ℕ) (hr : r ≤ ℓ) :
    (computePrefix r hr).length ≤ 3 * r := by
  induction r with
  | zero => simp [computePrefix]
  | succ r ih =>
    rw [computePrefix, List.length_append]
    have hw := writeBit_length (⟨r, by omega⟩ : Fin ℓ)
    have hl := ih (by omega)
    omega

theorem uncomputePrefix_run (r : ℕ) (hr : r ≤ ℓ) (x : Bits ℓ) :
    run (computePrefix r hr).reverse (encode x) = partialEncode r x := by
  have h := run_reverse_run (computePrefix r hr) (partialEncode r x)
  rw [computePrefix_run] at h
  exact h

/-- Exact computation from clean ancillas, using at most `3ℓ` primitives. -/
theorem compute_clean (x : Bits ℓ) :
    run (computePrefix ℓ le_rfl) (clean x) = encode x := by
  simpa using computePrefix_run ℓ le_rfl x

/-- Reversing the concrete program restores every comparator ancilla exactly to zero. -/
theorem uncompute_clean (x : Bits ℓ) :
    run (computePrefix ℓ le_rfl).reverse (encode x) = clean x := by
  simpa using uncomputePrefix_run ℓ le_rfl x

end OptimalQLS.TransducerCompiler.BinaryClock
