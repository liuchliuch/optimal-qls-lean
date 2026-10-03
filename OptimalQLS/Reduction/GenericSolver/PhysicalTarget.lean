import OptimalQLS.Reduction.GenericSolver.PhysicalInput
import OptimalQLS.Reduction.GenericSolver.BranchwiseSource

/-! The normalized source target, with only a permutation of computational
coordinates. Its inverse is the original logical inverse, never an inverse of
the singular zero-padded physical matrix. -/
noncomputable section
open scoped Classical
namespace OptimalQLS.Reduction.GenericSolver.Physical
open Matrix LowerBounds PhysicalPadding TransducerCompiler BinaryClock PolynomialTransform FreshCopies
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
variable {D : Type} [Fintype D] [DecidableEq D] {n : ℕ}

def sourceTarget (f : D ↪ Bits n) (α : ℝ) (A : Matrix D D ℂ) (b : EuclideanSpace ℂ D) :
    EuclideanSpace ℂ (Fin (dataRegister n).dimension ⊕ Fin (dataRegister n).dimension) :=
  WithLp.toLp 2 (fun j=>indexedVector (doubledRegister n)
    (WithLp.ofLp (dilationTarget f α A b)) (doubledIndex n j))

def CloseDilationSolution (f : D ↪ Bits n) (α : ℝ) (A : Matrix D D ℂ)
    (b : EuclideanSpace ℂ D) (ε : ℝ) (v : Fin (doubledRegister n).dimension → ℂ) : Prop :=
  ∃ y : EuclideanSpace ℂ (Fin (dataRegister n).dimension ⊕ Fin (dataRegister n).dimension),
    ‖y‖=1 ∧ ‖y-sourceTarget f α A b‖≤ε/2 ∧
    pureDensity v=bornMass v • pureDensity (fun i=>y ((doubledIndex n).symm i))

theorem sourceTarget_eq_right (f : D ↪ Bits n) {α : ℝ} (hα : 0<α)
    (A : Matrix D D ℂ) (hA : IsUnit A) (b : EuclideanSpace ℂ D) :
    sourceTarget f α A b=WithLp.toLp 2 (rightState (WithLp.ofLp (finiteSolutionTarget f A b))) := by
  unfold sourceTarget
  rw [indexed_dilationTarget f hα A hA b]
  congr 1
  funext j
  simp only [Equiv.symm_apply_apply]

theorem closeDilationSolution_iff (f : D ↪ Bits n) {α : ℝ} (hα : 0<α)
    (A : Matrix D D ℂ) (hA : IsUnit A) (b : EuclideanSpace ℂ D) (ε : ℝ)
    (v : Fin (doubledRegister n).dimension → ℂ) :
    CloseDilationSolution f α A b ε v ↔
      CloseDoubledState (doubledIndex n) (finiteSolutionTarget f A b) ε v := by
  unfold CloseDilationSolution CloseDoubledState
  rw [sourceTarget_eq_right f hα A hA b]

end OptimalQLS.Reduction.GenericSolver.Physical
