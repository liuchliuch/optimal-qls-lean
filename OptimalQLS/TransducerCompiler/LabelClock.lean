import OptimalQLS.TransducerCompiler.BinaryClock.Counts

/-! # Label-controlled clean binary clock updates -/

namespace OptimalQLS.TransducerCompiler.BinaryClock

variable {ℓ : ℕ}
abbrev LabelWire (ℓ : ℕ) := Fin 2 ⊕ Wire ℓ
abbrev LabelState (ℓ : ℕ) := LabelWire ℓ → Bool
abbrev LabelBits := Bool × Bool

def extend (label : LabelBits) (b : State ℓ) : LabelState ℓ
  | .inl i => if i = 0 then label.1 else label.2
  | .inr i => b i

/-- Place an existing comparator gate without touching the two label wires. -/
def liftGate : Gate (Wire ℓ) → Gate (LabelWire ℓ)
  | .x t => .x (.inr t)
  | .cx c t h => .cx (.inr c) (.inr t) (by simpa using h)
  | .ccx c d t hc hd => .ccx (.inr c) (.inr d) (.inr t)
      (by simpa using hc) (by simpa using hd)

theorem liftGate_act (g : Gate (Wire ℓ)) (label : LabelBits) (b : State ℓ) :
    (liftGate g).act (extend label b) = extend label (g.act b) := by
  ext w
  cases g <;> cases w <;> simp [liftGate, Gate.act, extend, Function.update_apply]

theorem liftProgram_run (p : Program (Wire ℓ)) (label : LabelBits) (b : State ℓ) :
    run (p.map liftGate) (extend label b) = extend label (run p b) := by
  induction p generalizing b with
  | nil => rfl
  | cons g gs ih => simp only [List.map_cons, run_cons, liftGate_act, ih]

/-- Turn the selected two-bit label into the all-one control value. -/
def negativeControls (code : LabelBits) : Program (LabelWire ℓ) :=
  (if code.1 then [] else [.x (.inl 0)]) ++ (if code.2 then [] else [.x (.inl 1)])

/-- One literal Toffoli, surrounded by at most four NOTs, selects any label. -/
def labelFlip (code : LabelBits) (target : Wire ℓ) : Program (LabelWire ℓ) :=
  negativeControls code ++ [.ccx (.inl 0) (.inl 1) (.inr target) (by simp) (by simp)] ++
    (negativeControls code).reverse

theorem labelFlip_length (code : LabelBits) (target : Wire ℓ) :
    (labelFlip code target).length ≤ 5 := by
  rcases code with ⟨a,b⟩
  cases a <;> cases b <;> simp [labelFlip, negativeControls]

theorem labelFlip_run (code label : LabelBits) (target : Wire ℓ) (b : State ℓ) :
    run (labelFlip code target) (extend label b) =
      extend label (if label = code then (Gate.x target).act b else b) := by
  rcases code with ⟨a,b'⟩
  rcases label with ⟨c,d⟩
  cases a <;> cases b' <;> cases c <;> cases d <;>
    ext w <;> cases w with
    | inl i => fin_cases i <;>
        simp [labelFlip, negativeControls, run, Gate.act, Function.update_apply, extend]
    | inr i =>
        by_cases hi : i = target <;>
          simp [labelFlip, negativeControls, run, Gate.act, Function.update_apply, extend, hi]

/-- A selected label flips each supported clock bit with at most five primitives. -/
def labelFlipPrefix (code : LabelBits) : (r : ℕ) → r ≤ ℓ → Bits ℓ → Program (LabelWire ℓ)
  | 0, _, _ => []
  | r+1, hr, mask => labelFlipPrefix code r (by omega) mask ++
      (if mask ⟨r, by omega⟩ then labelFlip code (.inl ⟨r, by omega⟩) else [])

theorem labelFlipPrefix_length (code : LabelBits) (r : ℕ) (hr : r ≤ ℓ) (mask : Bits ℓ) :
    (labelFlipPrefix code r hr mask).length ≤ 5 * r := by
  induction r with
  | zero => simp [labelFlipPrefix]
  | succ r ih =>
    rw [labelFlipPrefix, List.length_append]
    have hp := ih (by omega)
    have hnext := labelFlip_length code (.inl (⟨r, by omega⟩ : Fin ℓ))
    split <;> (try simp only [List.length_nil]) <;> omega

theorem labelFlipPrefix_run (code label : LabelBits) (r : ℕ) (hr : r ≤ ℓ)
    (mask : Bits ℓ) (b : State ℓ) :
    run (labelFlipPrefix code r hr mask) (extend label b) =
      extend label (if label = code then run (flipPrefix r hr mask) b else b) := by
  induction r with
  | zero => simp [labelFlipPrefix, flipPrefix, run]
  | succ r ih =>
    rw [labelFlipPrefix, run_append, ih]
    by_cases he : label = code
    · subst label
      simp only [ite_true]
      cases hm : mask ⟨r, by omega⟩ <;>
        simp [hm, labelFlip_run, flipPrefix, run_append, run]
    · cases hm : mask ⟨r, by omega⟩ <;>
        simp [hm, he, labelFlip_run, run]

/-- A real reversible selected-label update with an exact clean-comparator invariant. -/
def labelUpdate (code : LabelBits) (r : ℕ) (hr : r ≤ ℓ) (mask : Bits ℓ) : Program (LabelWire ℓ) :=
  (computePrefix r hr).reverse.map liftGate ++
    labelFlipPrefix code r hr mask ++ (computePrefix r hr).map liftGate

theorem labelUpdate_run (code label : LabelBits) (r : ℕ) (hr : r ≤ ℓ)
    (mask x : Bits ℓ) :
    run (labelUpdate code r hr mask) (extend label (encode x)) =
      extend label (encode (if label = code then xorLow r x mask else x)) := by
  simp only [labelUpdate, run_append, liftProgram_run, uncomputePrefix_run,
    labelFlipPrefix_run]
  by_cases he : label = code
  · simp only [he, ite_true, flipPrefix_partial, liftProgram_run, computePrefix_run]
  · simp only [he, ite_false, liftProgram_run, computePrefix_run]

theorem labelUpdate_length (code : LabelBits) (r : ℕ) (hr : r ≤ ℓ) (mask : Bits ℓ) :
    (labelUpdate code r hr mask).length ≤ 11 * r := by
  simp only [labelUpdate, List.length_append, List.length_map, List.length_reverse]
  have hc := computePrefix_length r hr
  have hm := labelFlipPrefix_length code r hr mask
  omega

end OptimalQLS.TransducerCompiler.BinaryClock
