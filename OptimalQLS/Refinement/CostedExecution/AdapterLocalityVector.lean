import OptimalQLS.Refinement.CostedExecution.AdapterLocalityHelpers
/-! # Literal full-bit tensor frames of the physical dilation adapter -/
noncomputable section
namespace OptimalQLS.Refinement.CostedExecution
open Matrix Preparation TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
open PhysicalProgram PhysicalMeasurement
open Reduction PhysicalAdapter
open scoped Classical
local instance : Nonempty Label := ⟨.pub⟩
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false


def adapterVectorEmbedding (a n ℓ : ℕ) :
    WireEmbedding phaseBits (adapterCoordinates a n ℓ) (adapterVectorFrame a n ℓ) := by
  refine ⟨⟨adapterMacroWire a n ℓ .preparation,?_⟩,?_,?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [adapterMacroWire,controlWire]
  · intro x r i
    rw [adapterVectorFrame_apply,preparation_vectorFrameRaw_wiring]
    rcases i with (i|(i|i))
    all_goals first | rfl | (fin_cases i <;> rfl)
  · intro x y r j hj
    rw [adapterVectorFrame_apply,adapterVectorFrame_apply,preparation_vectorFrameRaw_wiring,preparation_vectorFrameRaw_wiring]
    rcases j with (j|j)
    · rcases j with (j|j)
      · rcases j with (j|j)
        · rfl
        · rcases j with (j|j)
          · rcases j with (j|j)
            · rfl
            · rcases j with (j|j)
              · rfl
              · rcases j with (j|j)
                · exact False.elim (hj (.inr (.inl 0)) (by cases j; rfl))
                · rfl
          · rfl
      · revert hj
        refine Fin.cases (fun hj=>?_) (fun j hj=>?_) j
        · exact False.elim (hj (.inr (.inl 1)) rfl)
        · rfl
    · rcases j with (j|(j|j))
      · exact False.elim (hj (.inl ()) (by cases j; rfl))
      · exact False.elim (hj (.inr (.inr 0)) (by cases j; rfl))
      · exact False.elim (hj (.inr (.inr 1)) (by cases j; rfl))


end OptimalQLS.Refinement.CostedExecution
