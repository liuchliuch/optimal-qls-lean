import OptimalQLS.LowerBounds.HistoryNormExact

/-! The gauge-conjugated permutation is the literal cyclic gate sequence. -/
namespace OptimalQLS.LowerBounds

/-- Prefix-XOR gauge for an arbitrary reversible transition list. -/
def prefixProfile (gates : List Bool) : Fin gates.length → Bool :=
  fun j => xorFold (gates.take j.val)

theorem prefixProfile_succ_xor (gates : List Bool) [NeZero gates.length]
    (hclosed : xorFold gates = false) (j : Fin gates.length) :
    Bool.xor (prefixProfile gates j) (prefixProfile gates (j + 1)) = gates[j.val] := by
  have hval : (j + 1).val = (j.val + 1) % gates.length := by
    simp [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  have hj : j.val + 1 ≤ gates.length := by omega
  by_cases hlast : j.val + 1 = gates.length
  · have hzero : (j + 1).val = 0 := by rw [hval, hlast, Nat.mod_self]
    have hstep := xorFold_take_step gates j
    rw [hlast, List.take_length, hclosed, Bool.xor_false] at hstep
    simpa [prefixProfile, hzero] using hstep
  · have hlt : j.val + 1 < gates.length := by omega
    simp only [prefixProfile, hval, Nat.mod_eq_of_lt hlt]
    exact xorFold_take_step gates j

/-- Forward action is precisely `|j,b> ↦ |j+1,b XOR gate[j]>`, including
wraparound. Closure is proved for the padded parity sequence in HistoryGates. -/
theorem historyPermutation_prefixProfile_apply (gates : List Bool) [NeZero gates.length]
    (hclosed : xorFold gates = false) (j : Fin gates.length) (b : Bool) :
    historyPermutation (prefixProfile gates) (j, b) = (j + 1, Bool.xor b gates[j.val]) := by
  rw [historyPermutation_apply, prefixProfile_succ_xor gates hclosed]

theorem parityHistoryPermutation_apply (ell : ℕ) (z : List Bool)
    [NeZero (parityHistoryGates ell z).length]
    (j : Fin (parityHistoryGates ell z).length) (b : Bool) :
    historyPermutation (parityHistoryProfile ell z) (j, b) =
      (j + 1, Bool.xor b (parityHistoryGates ell z)[j.val]) := by
  exact historyPermutation_prefixProfile_apply _ (parityHistoryGates_xor ell z) j b

end OptimalQLS.LowerBounds
