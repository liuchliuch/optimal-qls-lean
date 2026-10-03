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


def preparationAdapterEmbedding (a n ℓ : ℕ) :
    WireEmbedding phaseBits (adapterCoordinates a n ℓ) (adapterMatrixFrame a n ℓ .preparation) := by
  refine ⟨⟨adapterMacroWire a n ℓ .preparation,?_⟩,?_,?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [adapterMacroWire,controlWire]
  · intro x r i
    rw [adapterMatrixFrame_apply,preparation_matrixFrameRaw_wiring]
    rcases i with (i|(i|i))
    all_goals first | rfl | (fin_cases i <;> rfl)
  · intro x y r j hj
    rw [adapterMatrixFrame_apply,adapterMatrixFrame_apply,preparation_matrixFrameRaw_wiring,preparation_matrixFrameRaw_wiring]
    rcases j with (j|j)
    · rcases j with (j|j)
      · rcases j with (j|j)
        · rcases j with (j|(j|j))
          · rfl
          · rfl
          · fin_cases j <;> first | rfl | exact False.elim (hj (.inr (.inl 0)) rfl)
        · rcases j with (j|j)
          · rcases j with (j|j)
            · rfl
            · rcases j with (j|j)
              · rfl
              · rcases j with (j|j)
                · first | rfl | exact False.elim (hj (.inr (.inl 0)) (by cases j; rfl))
                · rfl
          · rcases j with (j|j)
            · rcases j with (j|(j|j))
              · rfl
              · rfl
              · fin_cases j <;> first | rfl | exact False.elim (hj (.inr (.inl 0)) rfl)
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
