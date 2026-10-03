import OptimalQLS.TransducerCompiler.Basic

/-! # Concrete reversible bit-gate programs

The primitives are NOT, CNOT, and Toffoli. Toffoli is still counted as a
three-bit primitive here; a one- and two-qubit decomposition is a separate layer.
-/

namespace OptimalQLS.TransducerCompiler.BinaryClock

/-- A primitive gate, with its target distinct from every control. -/
inductive Gate (ι : Type*) where
  | x (target : ι)
  | cx (control target : ι) (distinct : control ≠ target)
  | ccx (first second target : ι) (first_distinct : first ≠ target)
      (second_distinct : second ≠ target)

variable {ι : Type*} [DecidableEq ι]

/-- Literal bit action of each primitive gate. -/
def Gate.act : Gate ι → (ι → Bool) → (ι → Bool)
  | .x t, b => Function.update b t (!(b t))
  | .cx c t _, b => Function.update b t (Bool.xor (b t) (b c))
  | .ccx c d t _ _, b => Function.update b t (Bool.xor (b t) (b c && b d))

theorem Gate.act_involutive (g : Gate ι) : Function.Involutive g.act := by
  intro b
  cases g with
  | x t =>
    ext i
    by_cases hi : i = t <;> simp [act, Function.update_apply, hi]
  | cx c t hc =>
    ext i
    by_cases hi : i = t <;> simp [act, Function.update_apply, hi, hc]
  | ccx c d t hc hd =>
    ext i
    by_cases hi : i = t <;> simp [act, Function.update_apply, hi, hc, hd]

/-- Every listed primitive is an actual reversible permutation of basis strings. -/
def Gate.equiv (g : Gate ι) : Equiv.Perm (ι → Bool) where
  toFun := g.act
  invFun := g.act
  left_inv := g.act_involutive
  right_inv := g.act_involutive

abbrev Program (ι : Type*) := List (Gate ι)

/-- Gates execute in their written order. -/
def run : Program ι → (ι → Bool) → (ι → Bool)
  | [], b => b
  | g :: gs, b => run gs (g.act b)

@[simp] theorem run_nil (b : ι → Bool) : run [] b = b := rfl
@[simp] theorem run_cons (g : Gate ι) (gs : Program ι) (b : ι → Bool) :
    run (g :: gs) b = run gs (g.act b) := rfl

theorem run_append (c d : Program ι) (b : ι → Bool) :
    run (c ++ d) b = run d (run c b) := by
  induction c generalizing b with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, run_cons, ih]

/-- Reversing a program is its exact inverse, since every primitive is involutive. -/
theorem run_reverse_run (c : Program ι) (b : ι → Bool) :
    run c.reverse (run c b) = b := by
  induction c generalizing b with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.reverse_cons, run_append, run_cons, run_nil, ih]
    exact g.act_involutive b

theorem run_run_reverse (c : Program ι) (b : ι → Bool) :
    run c (run c.reverse b) = b := by
  simpa using run_reverse_run c.reverse b

/-- A literal reversible permutation for the complete primitive-gate program. -/
def programEquiv (c : Program ι) : Equiv.Perm (ι → Bool) where
  toFun := run c
  invFun := run c.reverse
  left_inv := run_reverse_run c
  right_inv := run_run_reverse c

end OptimalQLS.TransducerCompiler.BinaryClock
