import Mathlib.Tactic

/-! # Exact counting of regularly scheduled oracle calls

A call is made at times `t` with `t % D = 0`, including time zero.
`scheduledCount D K` counts the calls among `0, ..., K-1`.
-/

namespace OptimalQLS.TransducerCompiler

/-- Number of scheduled calls strictly before time `K`, for period `D`. -/
def scheduledCount (D : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => scheduledCount D t + if t % D = 0 then 1 else 0

@[simp] theorem scheduledCount_zero (D : ℕ) : scheduledCount D 0 = 0 := rfl

@[simp] theorem scheduledCount_succ (D t : ℕ) :
    scheduledCount D (t + 1) = scheduledCount D t + if t % D = 0 then 1 else 0 := rfl

/-- There is exactly one call in any nonempty initial fragment of the first period. -/
theorem scheduledCount_first_fragment {D r : ℕ} (hr : r < D) :
    scheduledCount D (r + 1) = 1 := by
  induction r with
  | zero => simp [scheduledCount]
  | succ r ih =>
    have hr' : r < D := by omega
    rw [scheduledCount, ih hr', Nat.mod_eq_of_lt hr]
    simp

/-- The first full period contains just the call at time zero. -/
theorem scheduledCount_first_period {D : ℕ} (hD : 0 < D) :
    scheduledCount D D = 1 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hD)
  exact scheduledCount_first_fragment (Nat.lt_succ_self d)

/-- Adding one complete period adds precisely one scheduled call. -/
theorem scheduledCount_add_period {D : ℕ} (hD : 0 < D) (t : ℕ) :
    scheduledCount D (t + D) = scheduledCount D t + 1 := by
  induction t with
  | zero => simpa using scheduledCount_first_period hD
  | succ t ih =>
    rw [Nat.succ_add, scheduledCount, ih, scheduledCount]
    simp only [Nat.add_mod_right]
    omega

/-- Exactly `k` calls occur in `k` complete periods. -/
theorem scheduledCount_mul {D : ℕ} (hD : 0 < D) (k : ℕ) :
    scheduledCount D (D * k) = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, scheduledCount_add_period hD, ih]

/-- A divisible total budget has exactly the corresponding quotient of calls. -/
theorem scheduledCount_eq_div {D K : ℕ} (hD : 0 < D) (hdiv : D ∣ K) :
    scheduledCount D K = K / D := by
  obtain ⟨k, rfl⟩ := hdiv
  rw [scheduledCount_mul hD]
  simp [Nat.ne_of_gt hD]

/-- The recursive count is exactly the sum of the individual call indicators. -/
theorem scheduledCount_eq_sum (D K : ℕ) :
    scheduledCount D K = ∑ t ∈ Finset.range K, if t % D = 0 then 1 else 0 := by
  induction K with
  | zero => simp
  | succ K ih => simp only [scheduledCount_succ, Finset.sum_range_succ, ih]

@[simp] theorem scheduledCount_one (K : ℕ) : scheduledCount 1 K = K := by
  simpa using scheduledCount_mul (by decide : 0 < 1) K

/-- A budget `J` dividing total budget `K` is realized by period `K/J`. -/
theorem scheduledCount_quotient {K J : ℕ} (hK : 0 < K) (hJ : 0 < J)
    (hdiv : J ∣ K) : scheduledCount (K / J) K = J := by
  have hD : 0 < K / J := Nat.div_pos (Nat.le_of_dvd hK hdiv) hJ
  calc
    scheduledCount (K / J) K = scheduledCount (K / J) ((K / J) * J) := by
      rw [Nat.div_mul_cancel hdiv]
    _ = J := scheduledCount_mul hD J

end OptimalQLS.TransducerCompiler
