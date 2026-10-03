import OptimalQLS.Preparation.Finite
import OptimalQLS.GraphEncoding.Proposition43

noncomputable section
namespace OptimalQLS.Preparation
open Matrix TransducerCompiler GraphEncoding Geometry
variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The actual physical graph-register input is |01⟩ tensored with b. -/
def graphInput (b : EuclideanSpace ℂ D) : EuclideanSpace ℂ (Fin 4 × D) :=
  signalIsometry (1 : Fin 4) b

theorem graphInput_active (b : EuclideanSpace ℂ D) :
    graphInput b=activeTriple (blockTriple 0 b 0) := by
  ext ⟨g,i⟩
  fin_cases g <;> simp [graphInput,activeTriple,blockTriple]

theorem graphInput_norm (b : EuclideanSpace ℂ D) : ‖graphInput b‖=‖b‖ :=
  (signalIsometry (1 : Fin 4)).norm_map b

/-- Actual full source-oracle columns, including every unused graph sector. -/
theorem graphInput_source (Ub : Matrix.unitaryGroup D ℂ) (i₀ : D)
    (b : EuclideanSpace ℂ D) (hcol : ∀ i, Ub i i₀=b i) (i : Fin 4 × D) :
    (signalLift (S := Fin 4) Ub).val i (1,i₀)=graphInput b i := by
  rcases i with ⟨g,i⟩
  simp [signalLift,rewireUnitary,controlledOn,Matrix.blockDiagonal_apply,graphInput,hcol]

/-- All geometric hypotheses of the finite preparation theorem follow from
the original physical matrix, source vector, and condition bound. -/
theorem graphInput_promises (A : Matrix D D ℂ) (hA : A.IsHermitian)
    (hunit : IsUnit (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A))
    {κ : ℝ} (hκ : 0<κ)
    (hAnorm : ‖Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A‖≤1)
    (hinorm : ‖Ring.inverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A)‖≤κ)
    (b : EuclideanSpace ℂ D) (hb : ‖b‖=1) :
    let s := ‖Ring.inverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) b‖
    let H := graphMatrix A κ
    let e := graphInput b
    let P := (LinearMap.ker (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) H).toLinearMap).starProjection
    ‖e‖=1 ∧ s^2/(2*κ^2)≤‖P e‖^2 ∧ ‖P e‖^2≤s^2/κ^2 ∧
      0<‖P e‖^2 ∧ ‖P e‖^2≤1/2 ∧
      ‖Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ)
        (matrixPseudoInverse H (graphMatrix_hermitian A hA κ)) e‖≤s := by
  have hp := lemma42_projection_bounds _ (matrixHermitian_symmetric A hA)
    hunit hκ hAnorm hinorm b hb
  have hz := lemma42_pseudoinverse_bound _ (matrixHermitian_symmetric A hA)
    hunit hκ hAnorm hinorm b
  dsimp only
  rw [graphInput_norm,hb]
  refine ⟨rfl,?_⟩
  rw [graphInput_active,activeTriple_kernel_projection,activeTriple.norm_map,
    activeTriple_matrix_pseudoInverse A hA hκ,activeTriple.norm_map]
  exact ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,hz⟩

end OptimalQLS.Preparation
