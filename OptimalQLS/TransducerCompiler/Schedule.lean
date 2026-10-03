import Mathlib.Tactic

noncomputable section
namespace OptimalQLS.TransducerCompiler

/-- State of one query reservoir immediately before the next possible query.
Processed slots contain v; unprocessed slots contain Ov. -/
def track {α : Type*} [Zero α] (D t j : ℕ) (v q : α) : α :=
  if j < D then if t % D = 0 ∨ j < t % D then v else q else 0

/-- State of that reservoir after the scheduled query and before the work call. -/
def queriedTrack {α : Type*} [Zero α] (D t j : ℕ) (v q : α) : α :=
  if j < D then if j < t % D then v else q else 0

theorem track_zero {α : Type*} [Zero α] (D j : ℕ) (v q : α) :
    track D 0 j v q = if j < D then v else 0 := by simp [track]

theorem track_final {α : Type*} [Zero α] (D K j : ℕ) (v q : α) (h : D ∣ K) :
    track D K j v q = if j < D then v else 0 := by
  simp [track, Nat.mod_eq_zero_of_dvd h]

theorem queriedTrack_selected {α : Type*} [Zero α] (D t : ℕ) (v q : α)
    (hD : 0 < D) : queriedTrack D t (t % D) v q = q := by
  simp [queriedTrack, Nat.mod_lt _ hD]

theorem track_step_selected {α : Type*} [Zero α] (D t : ℕ) (v q : α)
    (hD : 0 < D) : track D (t+1) (t % D) v q = v := by
  have hm := Nat.mod_lt t hD
  have hstep : (t+1) % D = (t % D + 1) % D := by
    conv_lhs => rw [Nat.add_mod]
    conv_rhs => rw [Nat.add_mod]
    simp only [Nat.mod_mod]
  by_cases he : t % D + 1 = D
  · simp [track, hm, hstep, he]
  · have hl : t % D + 1 < D := by omega
    simp [track, hm, hstep, Nat.mod_eq_of_lt hl]

theorem track_step_other {α : Type*} [Zero α] (D t j : ℕ) (v q : α)
    (hD : 0 < D) (hj : j ≠ t % D) :
    track D (t+1) j v q = queriedTrack D t j v q := by
  have hm := Nat.mod_lt t hD
  have hstep : (t+1) % D = (t % D + 1) % D := by
    conv_lhs => rw [Nat.add_mod]
    conv_rhs => rw [Nat.add_mod]
    simp only [Nat.mod_mod]
  by_cases he : t % D + 1 = D
  · have h : j < D → j < t % D := by omega
    simp only [track, queriedTrack, hstep, he, Nat.mod_self, true_or, ite_true]
    by_cases hjD : j < D
    · simp [hjD, h hjD]
    · simp [hjD]
  · have hl : t % D + 1 < D := by omega
    have hn : t % D + 1 ≠ 0 := by omega
    have hj' : j < t % D + 1 ↔ j < t % D := by omega
    simp [track, queriedTrack, hstep, Nat.mod_eq_of_lt hl, hn, hj']

theorem track_nonboundary {α : Type*} [Zero α] (D t j : ℕ) (v q : α)
    (ht : t % D ≠ 0) : track D t j v q = queriedTrack D t j v q := by
  simp [track, queriedTrack, ht]

end OptimalQLS.TransducerCompiler
