import OptimalQLS.PhysicalRobustness.TruncatedStability
import OptimalQLS.PhysicalPadding.Input
import OptimalQLS.PhysicalPadding.Dimensions

/-!
# Physical noisy-input analytic endpoint

The full noisy block may mix used and unused computational coordinates.  Its
canonical high-spectral inverse, constructed from its actual spectral theorem,
has the paper's normalized `2κδ/α` stability.  Algorithmic realization of this
spectral truncation and its preparation costs is a distinct obligation.
-/
noncomputable section
namespace OptimalQLS.PhysicalRobustness
open PhysicalPadding Geometry Matrix
open scoped Matrix.Norms.L2Operator

variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

/-- The noisy full-register matrix need not be globally invertible.  The only
inverse used in the proof is the promised logical inverse of A. -/
theorem physical_truncated_solution_error (f : D ↪ P)
    (A : Matrix D D ℂ) (hA : A.IsHermitian) (hunit : IsUnit A)
    (B : Matrix P P ℂ) (hB : B.IsHermitian)
    (b : EuclideanSpace ℂ D) (hb : b ≠ 0)
    {α κ δ : ℝ} (hα : 0 < α) (hκ : 0 < κ) (hδ : 0 ≤ δ)
    (hinv : α*‖Ring.inverse A‖ ≤ κ) (hpert : ‖B-zeroExtend f A‖ ≤ δ)
    (hsmall : κ*δ/α ≤ 1/4) :
    let T := highInverse (Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) B)
      (matrixHermitian_symmetric B hB) δ
    let y := coordinateIsometry f
      (NormedSpace.normalize (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (Ring.inverse A) b))
    T (coordinateIsometry f b) ≠ 0 ∧
      ‖NormedSpace.normalize (T (coordinateIsometry f b))-y‖ ≤ 2*κ*δ/α := by
  let φ := Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ)
  let ψ := Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)
  let H := φ (zeroExtend f A)
  let C := φ B
  have hH : H.toLinearMap.IsSymmetric :=
    matrixHermitian_symmetric _ (zeroExtend_hermitian f A hA)
  have hC : C.toLinearMap.IsSymmetric := matrixHermitian_symmetric B hB
  have hAi : ‖Ring.inverse A‖ ≤ κ/α := (le_div_iff₀ hα).mpr (by nlinarith)
  have hψi : ‖Ring.inverse (ψ A)‖ ≤ κ/α := by
    rw [← Perturbation.toEuclideanCLM_inverse A hunit]
    exact hAi
  have hBA : ‖C-H‖ ≤ δ := by
    change ‖φ B-φ (zeroExtend f A)‖ ≤ δ
    rw [← map_sub]
    exact hpert
  have hkg : 0 < κ/α := div_pos hκ hα
  have hgap : ∀ i, |hC.eigenvalues rfl i| ≤ δ ∨ (κ/α)⁻¹-δ ≤ |hC.eigenvalues rfl i| := by
    intro i
    exact noisy_spectral_gap H C hH hC hδ
      (zeroExtend_spectral_gap f A hunit hH hkg hAi) hBA i
  have hs := truncated_solution_normalized_error (coordinateIsometry f) (ψ A)
    (hunit.map ψ.toMonoidHom) H C hC (zeroExtend_apply f A) hkg hδ hψi hBA
    (by convert hsmall using 1 <;> ring) hgap b hb
  rw [← Perturbation.toEuclideanCLM_inverse A hunit] at hs
  dsimp only
  refine ⟨hs.1,?_⟩
  calc
    _ ≤ 2*(κ/α)*δ := hs.2
    _ = 2*κ*δ/α := by ring

/-- Any actual output approximating the constructed truncated target inherits
the full requested additive error. This theorem does not assume or manufacture
an implementing circuit or a circuit resource bound. -/
theorem physical_approximate_truncated_output_error (f : D ↪ P)
    (A : Matrix D D ℂ) (hA : A.IsHermitian) (hunit : IsUnit A)
    (B : Matrix P P ℂ) (hB : B.IsHermitian)
    (b : EuclideanSpace ℂ D) (hb : b ≠ 0)
    {α κ δ ε : ℝ} (hα : 0 < α) (hκ : 0 < κ) (hδ : 0 ≤ δ)
    (hinv : α*‖Ring.inverse A‖ ≤ κ) (hpert : ‖B-zeroExtend f A‖ ≤ δ)
    (hsmall : κ*δ/α ≤ 1/4)
    (x : EuclideanSpace ℂ P)
    (hx : ‖x-NormedSpace.normalize
      (highInverse (Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) B)
        (matrixHermitian_symmetric B hB) δ (coordinateIsometry f b))‖ ≤ ε) :
    ‖x-coordinateIsometry f
      (NormedSpace.normalize (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (Ring.inverse A) b))‖
      ≤ ε+2*κ*δ/α := by
  have hs := (physical_truncated_solution_error f A hA hunit B hB b hb
    hα hκ hδ hinv hpert hsmall).2
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hx hs)

/-- Already at error zero, the full physical compression can be singular.
This rules out applying the ordinary inverse perturbation lemma to it. -/
theorem exact_physical_compression_can_be_singular {d : ℕ}
    (hpad : d < physicalDimension d) (A : Matrix (Fin d) (Fin d) ℂ) :
    ‖physicalMatrix A-physicalMatrix A‖ ≤ (0 : ℝ) ∧ ¬ IsUnit (physicalMatrix A) := by
  exact ⟨by simp, physicalMatrix_not_isUnit hpad A⟩

end OptimalQLS.PhysicalRobustness
