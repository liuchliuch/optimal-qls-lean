import OptimalQLS.TransducerCompiler.BinaryClock.Cycle

/-! # The real unitary matrix of a reversible primitive-gate program -/

noncomputable section
namespace OptimalQLS.TransducerCompiler.BinaryClock
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Linear extension of the actual basis-state permutation executed by the gate program. -/
def programUnitary (c : Program ι) : Matrix.unitaryGroup (ι → Bool) ℂ :=
  OptimalQLS.TransducerCompiler.permutation (programEquiv c).symm

theorem programUnitary_real (c : Program ι) (i j : ι → Bool) :
    ((programUnitary c : Matrix (ι → Bool) (ι → Bool) ℂ) i j).im = 0 :=
  OptimalQLS.TransducerCompiler.permutation_real _ _ _

/-- The matrix maps each basis vector to exactly the classical program's resulting basis vector. -/
theorem programUnitary_basis (c : Program ι) (b : ι → Bool) :
    (programUnitary c : Matrix (ι → Bool) (ι → Bool) ℂ) *ᵥ Pi.single b 1 =
      Pi.single (run c b) 1 := by
  rw [programUnitary, OptimalQLS.TransducerCompiler.permutation_apply]
  funext z
  have he : (programEquiv c).symm z = b ↔ z = run c b := by
    exact (Equiv.symm_apply_eq (programEquiv c)).trans Iff.rfl
  simp only [Function.comp_apply, Pi.single_apply, he]

/-- A comparator update is therefore a concrete real unitary with the proved encoded action. -/
theorem updatePrefix_unitary_basis {ℓ : ℕ} (r : ℕ) (hr : r ≤ ℓ) (mask x : Bits ℓ) :
    (programUnitary (updatePrefix r hr mask) : Matrix (State ℓ) (State ℓ) ℂ) *ᵥ
        Pi.single (encode x) 1 = Pi.single (encode (xorLow r x mask)) 1 := by
  rw [programUnitary_basis, updatePrefix_run]

/-- The full cycle returns each clean basis state exactly, including every comparator ancilla. -/
theorem cleanCycle_unitary_basis {ℓ : ℕ} (x : Bits ℓ) :
    (programUnitary (cleanCycle ℓ) : Matrix (State ℓ) (State ℓ) ℂ) *ᵥ
        Pi.single (clean x) 1 = Pi.single (clean x) 1 := by
  rw [programUnitary_basis, cleanCycle_run]

end OptimalQLS.TransducerCompiler.BinaryClock
