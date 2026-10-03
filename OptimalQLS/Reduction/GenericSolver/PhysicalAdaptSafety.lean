import OptimalQLS.Reduction.GenericSolver.PhysicalAdapt

/-! Physical safety of every node of the actual adapted branching tree. -/
noncomputable section
open scoped Classical
namespace OptimalQLS.Reduction.GenericSolver.FreshCopies
open Matrix LowerBounds PolynomialTransform TransducerCompiler BinaryClock
open Refinement.CostedExecution Physical
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
variable {P W D V : Type} [Fintype P] [DecidableEq P] [Fintype D] [DecidableEq D]
  {chart : P ≃ (W → Bool)} {dataChart : D ≃ (V → Bool)}

namespace PhysicalProgram
variable {G : Type*} {A B I J : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def Safe (gate : G → Matrix.unitaryGroup P ℂ) (argA : A ≃ (I → Bool)) (argB : B ≃ (J → Bool)) :
    PhysicalProgram G A B chart dataChart → Prop
  | .named g next => IsTwoLocal chart (gate g) ∧ next.Safe gate argA argB
  | .matrix p _ next => Nonempty (LiteralQueryPlacement argA chart p) ∧ next.Safe gate argA argB
  | .vector p _ next => Nonempty (LiteralQueryPlacement argB chart p) ∧ next.Safe gate argA argB
  | .measure _ next => ∀ b, (next b).Safe gate argA argB
  | .finish _ _ => True

theorem safe_prepend (gate : G → Matrix.unitaryGroup P ℂ) (argA : A ≃ (I → Bool)) (argB : B ≃ (J → Bool))
    (c : NamedCircuit G A B P) (next : PhysicalProgram G A B chart dataChart)
    (hg : ∀ g, NamedInstruction.gate g∈c → IsTwoLocal chart (gate g))
    (hA : ∀ p adj, NamedInstruction.matrixCall p adj∈c → Nonempty (LiteralQueryPlacement argA chart p))
    (hB : ∀ p adj, NamedInstruction.vectorCall p adj∈c → Nonempty (LiteralQueryPlacement argB chart p))
    (hn : next.Safe gate argA argB) : (prepend c next).Safe gate argA argB := by
  induction c with
  | nil => exact hn
  | cons i c ih =>
    have ht := ih (fun g h=>hg g (List.mem_cons_of_mem _ h))
      (fun p adj h=>hA p adj (List.mem_cons_of_mem _ h))
      (fun p adj h=>hB p adj (List.mem_cons_of_mem _ h))
    cases i with
    | gate g => exact ⟨hg g (by simp),ht⟩
    | matrixCall p adj => exact ⟨hA p adj (by simp),ht⟩
    | vectorCall p adj => exact ⟨hB p adj (by simp),ht⟩

end PhysicalProgram

namespace SourceProgram
variable {a n : ℕ}

theorem adapt_safe (F : TensorLayout chart dataChart) (c : SourceProgram chart a n) :
    (c.adapt F).Safe gateEval (matrixArguments a n) (Equiv.refl (Bits n)) := by
  induction c with
  | step i next ih =>
    apply PhysicalProgram.safe_prepend _ _ _ _ _ _ _ _ ih
    · intro g _
      exact gate_local g
    · intro p adj hp
      obtain ⟨F,rfl⟩ := (instructionCode_safe i).2.1 p adj hp
      exact ⟨matrixPlacement F⟩
    · intro p adj hp
      obtain ⟨F,rfl⟩ := (instructionCode_safe i).2.2 p adj hp
      exact ⟨vectorPlacement F⟩
  | measure i next ih => exact ih
  | finish flag => trivial

end SourceProgram
end OptimalQLS.Reduction.GenericSolver.FreshCopies
