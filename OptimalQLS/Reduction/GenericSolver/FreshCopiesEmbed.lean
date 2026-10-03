import OptimalQLS.Reduction.GenericSolver.FreshCopiesProcessBind
import OptimalQLS.Reduction.GenericSolver.PhysicalAdaptSafety

/-! Embed the actual supplied/adapted fixed-width physical tree in the
shrinking-register process without changing a single emitted operation. -/
noncomputable section
open scoped Classical
namespace OptimalQLS.Reduction.GenericSolver.FreshCopies
open Matrix LowerBounds PolynomialTransform TransducerCompiler
open Refinement.CostedExecution
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
variable {P W D V : Type} [Fintype P] [DecidableEq P] [Fintype W] [DecidableEq W]
  [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {chart : P ≃ (W → Bool)} {dataChart : D ≃ (V → Bool)}
variable {G : Type*} {A B VA VB : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

namespace PhysicalProgram

def toProcess (gate : G → Matrix.unitaryGroup P ℂ) (argA : A ≃ (VA → Bool)) (argB : B ≃ (VB → Bool)) :
    (p : PhysicalProgram G A B chart dataChart) → p.Safe gate argA argB →
      Process argA argB (Register.ofChart dataChart) (Register.ofChart chart)
  | .named g next,h => .unitary (gate g) h.1 (next.toProcess gate argA argB h.2)
  | .matrix p adj next,h => .matrix p adj (Classical.choice h.1) (next.toProcess gate argA argB h.2)
  | .vector p adj next,h => .vector p adj (Classical.choice h.1) (next.toProcess gate argA argB h.2)
  | .measure i next,h => .measure i (fun b=>(next b).toProcess gate argA argB (h b))
  | .finish F flag,_ => .trace (Q := Register.ofChart dataChart) F (.output flag)

theorem toProcess_lower (gate : G → Matrix.unitaryGroup P ℂ)
    (argA : A ≃ (VA → Bool)) (argB : B ≃ (VB → Bool))
    (p : PhysicalProgram G A B chart dataChart) (h : p.Safe gate argA argB) :
    (p.toProcess gate argA argB h).lower=p.lower gate := by
  induction p with
  | named g next ih => simp [toProcess,Process.lower,lower,Register.ofChart,indexedMatrix,finiteMatrix,ih]
  | matrix p adj next ih => simp [toProcess,Process.lower,lower,Register.ofChart,indexedMatrix,finiteMatrix,ih]
  | vector p adj next ih => simp [toProcess,Process.lower,lower,Register.ofChart,indexedMatrix,finiteMatrix,ih]
  | measure i next ih => simp [toProcess,Process.lower,lower,Register.ofChart,indexedMatrix,finiteMatrix,ih]
  | finish F flag => rfl

theorem toProcess_resources (gate : G → Matrix.unitaryGroup P ℂ)
    (argA : A ≃ (VA → Bool)) (argB : B ≃ (VB → Bool))
    (p : PhysicalProgram G A B chart dataChart) (h : p.Safe gate argA argB) :
    (p.toProcess gate argA argB h).work=p.work ∧
    (p.toProcess gate argA argB h).measurements=p.measurements ∧
    (p.toProcess gate argA argB h).matrixCalls=p.matrixCalls ∧
    (p.toProcess gate argA argB h).vectorCalls=p.vectorCalls := by
  induction p with
  | named g next ih => simp [toProcess,Process.work,Process.measurements,Process.matrixCalls,
      Process.vectorCalls,work,measurements,matrixCalls,vectorCalls,ih]
  | matrix p adj next ih => simp [toProcess,Process.work,Process.measurements,Process.matrixCalls,
      Process.vectorCalls,work,measurements,matrixCalls,vectorCalls,ih]
  | vector p adj next ih => simp [toProcess,Process.work,Process.measurements,Process.matrixCalls,
      Process.vectorCalls,work,measurements,matrixCalls,vectorCalls,ih]
  | measure i next ih => simp [toProcess,Process.work,Process.measurements,Process.matrixCalls,
      Process.vectorCalls,work,measurements,matrixCalls,vectorCalls,ih]
  | finish F flag => exact ⟨rfl,rfl,rfl,rfl⟩

end PhysicalProgram
end OptimalQLS.Reduction.GenericSolver.FreshCopies
