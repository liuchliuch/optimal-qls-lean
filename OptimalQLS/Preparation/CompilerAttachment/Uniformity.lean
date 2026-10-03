import OptimalQLS.Preparation.CompilerAttachment.FullCompiler
import OptimalQLS.Preparation.OriginalState

/-! # Literal preparation code is independent of the hidden exact solution scale -/
noncomputable section
set_option synthInstance.maxSize 8192
open scoped Classical
namespace OptimalQLS.Preparation.CompilerAttachment
open Matrix TransducerCompiler BinaryClock PolynomialTransform

theorem preparationWorkCode_uniform (a : ℕ) {κ s t ŝ : ℝ}
    (h : BudgetParameters κ s ŝ) (h' : BudgetParameters κ t ŝ) :
    preparationWorkCode a h=preparationWorkCode a h' := rfl

theorem instruction_uniform (a n ℓ : ℕ) {κ s t ŝ : ℝ}
    (h : BudgetParameters κ s ŝ) (h' : BudgetParameters κ t ŝ) (graph : GraphCircuit a n ℓ) :
    instruction a n ℓ h graph=instruction a n ℓ h' graph := rfl

theorem originalPreparedState_uniform (a n : ℕ) {κ s t ŝ : ℝ}
    (h : BudgetParameters κ s ŝ) (h' : BudgetParameters κ t ŝ)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    originalPreparedState (fun _ : Fin a=>false) (fun _ : Fin n=>false) h UA Ub=
      originalPreparedState (fun _ : Fin a=>false) (fun _ : Fin n=>false) h' UA Ub := rfl

end OptimalQLS.Preparation.CompilerAttachment
