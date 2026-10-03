import OptimalQLS.LowerBounds.ParityHistoryFamily

/-!
# Concrete two-bit-query simulation of the history transition

The oracle here is exactly `|i,a,w> -> |i,a XOR z_i,w>`. A fixed reversible
index computation, two literal oracle calls, a fixed controlled work-X, and
uncomputation implement the history transition on clean scratch registers.
All maps are actual finite permutations; no query-cost certificate or
input-dependent free gate is used.
-/
noncomputable section
namespace OptimalQLS.LowerBounds

abbrev SimulationBasis (N m : ℕ) := Fin m × Bool × HistoryBasis N

def standardBitQueryMap {N m : ℕ} (z : BitString m) (b : SimulationBasis N m) :
    SimulationBasis N m := (b.1, Bool.xor b.2.1 (z b.1), b.2.2)

def standardBitQuery {N m : ℕ} (z : BitString m) : Equiv.Perm (SimulationBasis N m) :=
  (show Function.Involutive (standardBitQueryMap z) from by
    rintro ⟨i, a, j, b⟩
    cases a <;> cases hz : z i <;> simp [standardBitQueryMap, hz]).toPerm

def labelBit {m : ℕ} (z : BitString m) : Option (Fin m) → Bool
  | none => false
  | some i => z i

/-- Input-independent reversible computation of a clock's query address. -/
def computeHistoryIndex {N m : ℕ} [NeZero m] (label : Fin N → Option (Fin m)) :
    Equiv.Perm (SimulationBasis N m) where
  toFun b := (b.1 + (label b.2.2.1).getD 0, b.2)
  invFun b := (b.1 - (label b.2.2.1).getD 0, b.2)
  left_inv b := by rcases b with ⟨i, a, j, b⟩; simp
  right_inv b := by rcases b with ⟨i, a, j, b⟩; simp

/-- The queried scratch bit toggles the work bit only on active clock transitions. -/
def selectHistoryWorkMap {N m : ℕ} (label : Fin N → Option (Fin m))
    (b : SimulationBasis N m) : SimulationBasis N m :=
  (b.1, b.2.1, b.2.2.1, Bool.xor b.2.2.2 (b.2.1 && (label b.2.2.1).isSome))

def selectHistoryWork {N m : ℕ} (label : Fin N → Option (Fin m)) :
    Equiv.Perm (SimulationBasis N m) :=
  (show Function.Involutive (selectHistoryWorkMap label) from by
    rintro ⟨i, a, j, b⟩
    cases a <;> cases b <;> cases h : label j <;> simp [selectHistoryWorkMap, h]).toPerm

def advanceHistoryClock {N m : ℕ} [NeZero N] : Equiv.Perm (SimulationBasis N m) :=
  (Equiv.refl (Fin m)).prodCongr ((Equiv.refl Bool).prodCongr (clockShift N))

/-- Two occurrences of the literal standard oracle, separated by known gates. -/
def twoQueryHistoryStep {N m : ℕ} [NeZero N] [NeZero m]
    (label : Fin N → Option (Fin m)) (z : BitString m) : Equiv.Perm (SimulationBasis N m) :=
  (computeHistoryIndex label).trans <| (standardBitQuery z).trans <|
    (selectHistoryWork label).trans <| (standardBitQuery z).trans <|
      (computeHistoryIndex label).symm.trans advanceHistoryClock

/-- Exact coherent clean-scratch action of that concrete two-query sequence. -/
theorem twoQueryHistoryStep_clean {N m : ℕ} [NeZero N] [NeZero m]
    (label : Fin N → Option (Fin m)) (z : BitString m) (j : Fin N) (b : Bool) :
    twoQueryHistoryStep label z (0, false, j, b) =
      (0, false, j + 1, Bool.xor b (labelBit z (label j))) := by
  cases hl : label j with
  | none =>
    cases hz : z 0 <;> cases b <;>
      simp [twoQueryHistoryStep, computeHistoryIndex, standardBitQuery, standardBitQueryMap,
        selectHistoryWork, selectHistoryWorkMap, advanceHistoryClock, labelBit, hl, hz]
  | some i =>
    cases hz : z i <;> cases b <;>
      simp [twoQueryHistoryStep, computeHistoryIndex, standardBitQuery, standardBitQueryMap,
        selectHistoryWork, selectHistoryWorkMap, advanceHistoryClock, labelBit, hl, hz]

/-- Input-independent labels of the exact forward/padding/reverse transition list. -/
def parityHistoryLabels (ell m : ℕ) : List (Option (Fin m)) :=
  ((List.replicate (ell - 1) none ++ List.ofFn (fun i : Fin m => some i)) ++
    List.replicate ell none) ++ ((List.ofFn (fun i : Fin m => some i)).reverse ++ [none])

@[simp] theorem parityHistoryLabels_length {ell m : ℕ} (hell : 0 < ell) :
    (parityHistoryLabels ell m).length = 2 * ell + 2 * m := by
  simp [parityHistoryLabels]
  omega

/-- Evaluating those fixed labels with z yields exactly Definition6.2's gates. -/
theorem parityHistoryLabels_map {ell m : ℕ} (z : BitString m) :
    (parityHistoryLabels ell m).map (labelBit z) = parityHistoryGates ell (List.ofFn z) := by
  simp [parityHistoryLabels, parityHistoryGates, List.map_ofFn, labelBit, Function.comp_def]

def parityHistoryLabel {N ell m : ℕ} (hell : 0 < ell) (hN : N = 2 * ell + 2 * m) :
    Fin N → Option (Fin m) :=
  fun j => (parityHistoryLabels ell m).get ⟨j.val, by
    rw [parityHistoryLabels_length hell, ← hN]
    exact j.isLt⟩

/-- Exact bit-query implementation of the paper's history permutation. -/
theorem parityHistoryStep_twoQuery_clean {N ell m : ℕ} [NeZero N] [NeZero m]
    (hell : 0 < ell) (hN : N = 2 * ell + 2 * m) (z : BitString m)
    (j : Fin N) (b : Bool) :
    twoQueryHistoryStep (parityHistoryLabel hell hN) z (0, false, j, b) =
      (0, false, historyPermutation (fixedParityProfile ell z) (j, b)) := by
  rw [twoQueryHistoryStep_clean, fixedParityProfile_transition hell hN z j b]
  congr 2
  have hmap := parityHistoryLabels_map (ell := ell) z
  have hi : j.val < (parityHistoryLabels ell m).length := by
    rw [parityHistoryLabels_length hell, ← hN]
    exact j.isLt
  have higr : j.val < (parityHistoryGates ell (List.ofFn z)).length := by
    rw [parityHistoryGates_length (by omega), List.length_ofFn, ← hN]
    exact j.isLt
  have he := congrArg (fun l : List Bool => l[j.val]?) hmap
  simpa [parityHistoryLabel, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem higr, List.getElem?_map] using he

end OptimalQLS.LowerBounds
