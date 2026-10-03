import OptimalQLS.LowerBounds.HermitianDilation
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A full state-preparation unitary for every concrete finite unit vector

The unitary is constructed by extending the single prescribed state to an
orthonormal basis. Its entire matrix is fixed by the source vector, rather
than leaving the other columns unconstrained in an oracle specification.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix

variable {D : Type*} [Fintype D] [DecidableEq D]

theorem exists_statePreparationUnitary (i₀ : D) (b : D → ℂ)
    (hb : ‖WithLp.toLp 2 b‖ = 1) :
    ∃ U : Matrix.unitaryGroup D ℂ, ∀ i, U i i₀ = b i := by
  let v : D → EuclideanSpace ℂ D := fun _ => WithLp.toLp 2 b
  have hv : Orthonormal ℂ (({i₀} : Set D).restrict v) := by
    constructor
    · intro i; exact hb
    · intro i j hij
      have hi : i.val = i₀ := Set.mem_singleton_iff.mp i.property
      have hj : j.val = i₀ := Set.mem_singleton_iff.mp j.property
      exact (hij (Subtype.ext (hi.trans hj.symm))).elim
  obtain ⟨basis, hbasis⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (show Module.finrank ℂ (EuclideanSpace ℂ D) = Fintype.card D from
      finrank_euclideanSpace)
  let standard := EuclideanSpace.basisFun D ℂ
  refine ⟨⟨standard.toBasis.toMatrix basis, standard.toMatrix_orthonormalBasis_mem_unitary basis⟩, ?_⟩
  intro i
  change (standard.toBasis.toMatrix basis) i i₀ = b i
  rw [Module.Basis.toMatrix_apply, hbasis i₀ (Set.mem_singleton i₀)]
  rfl

/-- A selected entire preparation matrix, depending only on b and the fixed
computational input index. Proof arguments do not affect the selected value. -/
def statePreparationUnitary (i₀ : D) (b : D → ℂ) (hb : ‖WithLp.toLp 2 b‖ = 1) :
    Matrix.unitaryGroup D ℂ := Classical.choose (exists_statePreparationUnitary i₀ b hb)

theorem statePreparationUnitary_prepares (i₀ : D) (b : D → ℂ) (hb : ‖WithLp.toLp 2 b‖ = 1) :
    ∀ i, statePreparationUnitary i₀ b hb i i₀ = b i :=
  Classical.choose_spec (exists_statePreparationUnitary i₀ b hb)

theorem statePreparationUnitary_eq_of_source_eq (i₀ : D) (b c : D → ℂ)
    (hb : ‖WithLp.toLp 2 b‖ = 1) (hc : ‖WithLp.toLp 2 c‖ = 1) (hbc : b = c) :
    statePreparationUnitary i₀ b hb = statePreparationUnitary i₀ c hc := by
  subst c
  rfl

end OptimalQLS.LowerBounds
