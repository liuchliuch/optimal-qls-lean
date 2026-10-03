import OptimalQLS.TransducerCompiler.Reservoir
import OptimalQLS.TransducerCompiler.ClockPreparation

noncomputable section
namespace OptimalQLS.TransducerCompiler
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {K : ℕ}

/-- Clock-only unitary: it never operates on the data or the label. -/
def clockLift (P : Matrix.unitaryGroup (Fin K) ℂ) : Matrix.unitaryGroup (Space n K) ℂ :=
  rewireUnitary (Equiv.prodComm (Fin K) (Base n))
    (controlledOn (fun _ : Base n => true) P)

theorem clockLift_apply (P : Matrix.unitaryGroup (Fin K) ℂ)
    (v : Space n K → ℂ) (i : Base n) (k : Fin K) :
    ((clockLift (n := n) P : Matrix (Space n K) (Space n K) ℂ) *ᵥ v) (i,k) =
      ((P : Matrix (Fin K) (Fin K) ℂ) *ᵥ fun j => v (i,j)) k := by
  rw [clockLift, rewire_apply]
  simp [Function.comp_def]

/-- All clock-only compilation gates have real coefficients. -/
theorem clockLift_real (P : Matrix.unitaryGroup (Fin K) ℂ)
    (hP : ∀ i j, (P.val i j).im = 0) (i j : Space n K) :
    ((clockLift (n := n) P : Matrix (Space n K) (Space n K) ℂ) i j).im = 0 := by
  change (if i.1 = j.1 then P.val i.2 j.2 else (0 : ℂ)).im = 0
  split_ifs
  · exact hP _ _
  · rfl



end OptimalQLS.TransducerCompiler
