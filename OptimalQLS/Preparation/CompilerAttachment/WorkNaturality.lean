import OptimalQLS.Preparation.WorkGates.Complete
import OptimalQLS.Preparation.CompilerBridge

/-! # Entrywise physical-signal naturality of the already synthesized preparation work -/
noncomputable section
set_option synthInstance.maxSize 4096
namespace OptimalQLS.Preparation.CompilerAttachment
open Matrix TransducerCompiler WorkGates
variable {S D : Type*} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]

def workLabelMatrix {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) (q : Bool) : Matrix (Fin 8) (Fin 8) ℂ :=
  labelOperation hμ hr q 8 * labelOperation hμ hr q 7 *
    labelOperation hμ hr q 6 * labelOperation hμ hr q 5 *
    labelOperation hμ hr q 4 * labelOperation hμ hr q 3 *
    labelOperation hμ hr q 2 * labelOperation hμ hr q 1 * labelOperation hμ hr q 0

theorem preparationWork_fiber (s₀ : S) {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1) :
    (preparationWork (signalProjector (D := D) s₀) (signalProjector_star s₀)
      (signalProjector_idempotent s₀) hμ hr).val=
      fiberMatrix (fun x : S × D => workLabelMatrix hμ hr (decide (x.1=s₀))) := by
  rw [preparationWork_factorization]
  simp only [workOperation,fiberMatrix_mul]
  rfl

theorem compilerWork_entries (s₀ : S) {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    (b c : Bool) (s t : S) (i j : D) (l m : Label) :
    (compilerWork (signalProjector (D := D) s₀) (signalProjector_star s₀)
      (signalProjector_idempotent s₀) hμ hr).val ((b,(s,i)),l) ((c,(t,j)),m)=
      if (s,i)=(t,j) then workLabelMatrix hμ hr (decide (s=s₀))
        (compilerLabel (b,l)) (compilerLabel (c,m)) else 0 := by
  change (preparationWork (signalProjector (D := D) s₀) (signalProjector_star s₀)
      (signalProjector_idempotent s₀) hμ hr).val
    (compilerWiring (S × D) ((b,(s,i)),l)) (compilerWiring (S × D) ((c,(t,j)),m))=_
  rw [preparationWork_fiber]
  rfl

end OptimalQLS.Preparation.CompilerAttachment
