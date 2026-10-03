import OptimalQLS.PhysicalPadding.Preparation
import OptimalQLS.PhysicalPadding.Input
import OptimalQLS.PhysicalPadding.Filter
import OptimalQLS.Refinement.Analytic

/-!
# Literal polynomial refinement of the physical accepted preparation

Both the filter and correction below are the existing constructed polynomials.
Their exact active-space transport is proved from operator intertwining.  Only
the original logical matrix is inverted; the physical matrix may be singular.
-/

noncomputable section
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000
namespace OptimalQLS.PhysicalPadding

open Matrix Polynomial PolynomialTransform GraphEncoding Preparation Refinement
open scoped BigOperators Matrix.Norms.L2Operator

variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

/-- The literal kernel-filter polynomial used by the refinement branch. -/
def refinementFilter (A : Matrix D D ℂ) (κ ε : ℝ) :
    EuclideanSpace ℂ (Fin 4 × D) →L[ℂ] EuclideanSpace ℂ (Fin 4 × D) :=
  polynomialOperator (kernelFilter (graphFilterGap κ) (ε / 1024))
    (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (normalizedGraph A κ))

/-- The actual accepted vector: filter, select graph label 2, then apply the
literal correction polynomial with the same refinement error budget. -/
def refinementAccepted (A : Matrix D D ℂ) (κ ε : ℝ)
    (y : EuclideanSpace ℂ (Fin 4 × D)) : EuclideanSpace ℂ D :=
  correctionOperator A κ (ε / 1024) (graphCoordinate 2 (refinementFilter A κ ε y))

theorem normalized_graph_apply (f : D ↪ P) (A : Matrix D D ℂ) (κ : ℝ)
    (x : EuclideanSpace ℂ (Fin 4 × D)) :
    Matrix.toEuclideanCLM (n := Fin 4 × P) (𝕜 := ℂ) (normalizedGraph (zeroExtend f A) κ)
      (graphIsometry f x) =
      graphIsometry f (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ)
        (normalizedGraph A κ) x) := by
  simp only [normalizedGraph, RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul,
    ContinuousLinearMap.smul_apply, graph_apply]

/-- Every real polynomial of the normalized graph preserves the exact active
copy, including its nonzero constant term. -/
theorem normalized_graph_polynomial (f : D ↪ P) (A : Matrix D D ℂ) (κ : ℝ)
    (p : ℝ[X]) (x : EuclideanSpace ℂ (Fin 4 × D)) :
    polynomialOperator p (Matrix.toEuclideanCLM (n := Fin 4 × P) (𝕜 := ℂ)
      (normalizedGraph (zeroExtend f A) κ)) (graphIsometry f x) =
      graphIsometry f (polynomialOperator p (Matrix.toEuclideanCLM
        (n := Fin 4 × D) (𝕜 := ℂ) (normalizedGraph A κ)) x) :=
  intertwining_polynomialOperator (graphIsometry f) _ _ (normalized_graph_apply f A κ) p x

theorem refinementFilter_isometry (f : D ↪ P) (A : Matrix D D ℂ) (κ ε : ℝ)
    (x : EuclideanSpace ℂ (Fin 4 × D)) :
    refinementFilter (zeroExtend f A) κ ε (graphIsometry f x) =
      graphIsometry f (refinementFilter A κ ε x) :=
  normalized_graph_polynomial f A κ _ x

/-- Graph postselection commutes with literal data-coordinate insertion. -/
theorem graphCoordinate_isometry (f : D ↪ P) (g : Fin 4)
    (x : EuclideanSpace ℂ (Fin 4 × D)) :
    graphCoordinate g (graphIsometry f x) = coordinateIsometry f (graphCoordinate g x) := by
  ext p
  simp [graphCoordinate, coordinateIsometry_apply, Matrix.mulVec, dotProduct,
    insertion, basisInsertion, graphIndex, Fintype.sum_prod_type, ite_and]

/-- The correction is the genuine polynomial of the singular physical data
operator; its action on the active copy equals the logical correction. -/
theorem correctionOperator_isometry (f : D ↪ P) (A : Matrix D D ℂ) (κ η : ℝ)
    (x : EuclideanSpace ℂ D) :
    correctionOperator (zeroExtend f A) κ η (coordinateIsometry f x) =
      coordinateIsometry f (correctionOperator A κ η x) := by
  unfold correctionOperator
  rw [polynomial_matrix_to_operator, polynomial_matrix_to_operator]
  exact zeroExtend_polynomial f A _ x

/-- Exact transport of the actual accepted physical vector, not an assumed
support-preservation certificate. -/
theorem refinementAccepted_isometry (f : D ↪ P) (A : Matrix D D ℂ) (κ ε : ℝ)
    (x : EuclideanSpace ℂ (Fin 4 × D)) :
    refinementAccepted (zeroExtend f A) κ ε (graphIsometry f x) =
      coordinateIsometry f (refinementAccepted A κ ε x) := by
  unfold refinementAccepted
  rw [refinementFilter_isometry, graphCoordinate_isometry, correctionOperator_isometry]

theorem graph_kernelProjector_isometry (f : D ↪ P) (A : Matrix D D ℂ)
    (hA : A.IsHermitian) (κ : ℝ) (x : EuclideanSpace ℂ (Fin 4 × D)) :
    Alignment.kernelProjector (graphMatrix (zeroExtend f A) κ) (graphIsometry f x) =
      graphIsometry f (Alignment.kernelProjector (graphMatrix A κ) x) := by
  simpa only [matrixKernelProjection, StarAlgEquiv.apply_symm_apply, Alignment.kernelProjector]
    using graph_kernel_projection f A hA κ x

theorem graph_normalizedProjectedInput_isometry (f : D ↪ P) (A : Matrix D D ℂ)
    (hA : A.IsHermitian) (κ : ℝ) (b : EuclideanSpace ℂ D) :
    Alignment.normalizedProjectedInput (graphMatrix (zeroExtend f A) κ)
      (graphInput (coordinateIsometry f b)) =
      graphIsometry f (Alignment.normalizedProjectedInput (graphMatrix A κ) (graphInput b)) := by
  change NormedSpace.normalize
    (Alignment.kernelProjector (graphMatrix (zeroExtend f A) κ)
      (graphInput (coordinateIsometry f b))) =
    graphIsometry f (NormedSpace.normalize (Alignment.kernelProjector (graphMatrix A κ) (graphInput b)))
  rw [graphInput_isometry, graph_kernelProjector_isometry f A hA, isometry_normalize]

/-- Global filter accuracy follows from the singular-safe physical graph
spectrum, so the exact polynomial used in refinement needs no inverse. -/
theorem refinementFilter_error (A : Matrix D D ℂ) (hA : A.IsHermitian)
    (hAnorm : ‖A‖ ≤ 1) {κ ε : ℝ} (hκ : 2 ≤ κ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    ‖refinementFilter A κ ε - Alignment.kernelProjector (graphMatrix A κ)‖ ≤ ε / 1024 := by
  have hk : 0 < κ := by linarith
  have hη : 0 < ε / 1024 := by positivity
  have hη1 : ε / 1024 < 1 / 2 := by linarith
  have hd : 0 < graphFilterGap κ ∧ graphFilterGap κ ≤ 1 / Real.sqrt 12 :=
    ⟨graphFilterGap_pos hk, min_le_right _ _⟩
  unfold refinementFilter Alignment.kernelProjector
  rw [← normalizedGraph_kernel_projection A hk]
  have hs : (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ)
      (normalizedGraph A κ)).toLinearMap.IsSymmetric :=
    Matrix.isHermitian_iff_isSymmetric.mp (normalizedGraph_hermitian A hA κ)
  apply kernelFilter_operator_bound _ hs hd.1 hd.2 hη hη1
  intro μ hmem hμ
  obtain ⟨hlo, hup⟩ := normalized_graph_spectrum_singular_safe A hA hκ hAnorm μ hmem hμ
  refine ⟨(min_le_left _ _).trans ?_, hup⟩
  simpa only [graphNormalization] using hlo

/-- Refinement on an actually supported physical coarse vector inherits the
logical error and success probability.  Only the logical matrix is invertible. -/
theorem physical_refinement_component_guarantee (f : D ↪ P)
    (A : Matrix D D ℂ) (hA : A.IsHermitian) (hunit : IsUnit A) (hAnorm : ‖A‖ ≤ 1)
    {κ ε : ℝ} (hκ : 2 ≤ κ) (hinorm : ‖Ring.inverse A‖ ≤ κ)
    (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (b : EuclideanSpace ℂ D) (hb : ‖b‖ = 1)
    (yphys : EuclideanSpace ℂ (Fin 4 × P)) (hy : ‖yphys‖ ≤ 1)
    (hsupport : ∃ y : EuclideanSpace ℂ (Fin 4 × D), yphys = graphIsometry f y)
    {β : ℝ} (hβ0 : 1 / 32 ≤ β) (hβ1 : β ≤ 1)
    (hPy : Alignment.kernelProjector (graphMatrix (zeroExtend f A) κ) yphys =
      β • Alignment.normalizedProjectedInput (graphMatrix (zeroExtend f A) κ)
        (graphInput (coordinateIsometry f b))) :
    let z := refinementAccepted (zeroExtend f A) κ ε yphys
    let x := coordinateIsometry f
      (NormedSpace.normalize (Ring.inverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) b))
    z ≠ 0 ∧ ‖NormedSpace.normalize z - x‖ ≤ ε / 2 ∧ 1 / 65536 < ‖z‖ ^ 2 := by
  obtain ⟨y, rfl⟩ := hsupport
  have hy' : ‖y‖ ≤ 1 := by simpa only [(graphIsometry f).norm_map] using hy
  have hPy' : Alignment.kernelProjector (graphMatrix A κ) y =
      β • Alignment.normalizedProjectedInput (graphMatrix A κ) (graphInput b) := by
    apply (graphIsometry f).injective
    rw [graph_kernelProjector_isometry f A hA,
      graph_normalizedProjectedInput_isometry f A hA] at hPy
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul] using hPy
  have hz := refinement_component_guarantee A hA hunit hAnorm hκ hinorm hε0 hε1
    b hb y hy' hβ0 hβ1 hPy' (refinementFilter A κ ε)
    (refinementFilter_error A hA hAnorm hκ hε0 hε1)
  change refinementAccepted A κ ε y ≠ 0 ∧
    ‖NormedSpace.normalize (refinementAccepted A κ ε y) -
      NormedSpace.normalize (Ring.inverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) b)‖ ≤ ε / 2 ∧
    1 / 65536 < ‖refinementAccepted A κ ε y‖ ^ 2 at hz
  dsimp only
  rw [refinementAccepted_isometry, isometry_normalize, isometry_norm_sub,
    (coordinateIsometry f).norm_map]
  refine ⟨?_, hz.2.1, hz.2.2⟩
  intro hzero
  exact hz.1 ((coordinateIsometry f).injective (by simpa using hzero))

/-- The genuine supplied-oracle preparation followed by the existing literal
filter and correction polynomials has the physical normalized-solution error
and constant success bound.  Active support and the real kernel coefficient
are derived from preparation, rather than additional output assumptions. -/
theorem physical_preparation_refinement_guarantee
    {S : Type*} [Fintype S] [DecidableEq S] {d : ℕ} [NeZero d]
    (s₀ : S) {κ s ŝ ε : ℝ} (h : TransducerCompiler.BudgetParameters κ s ŝ)
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (hunit : IsUnit A)
    (hinv : ‖Ring.inverse A‖ ≤ κ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (UA : Matrix.unitaryGroup (S × PhysicalData d) ℂ)
    (henc : IsBlockEncoding s₀ 1 0 UA (physicalMatrix A))
    (Ub : Matrix.unitaryGroup (PhysicalData d) ℂ)
    (b : DataSpace d) (hb : ‖b‖ = 1)
    (hcol : ∀ i, Ub i 0 = activeIsometry d b i)
    (hs : s = solutionScale 1 A b) :
    let Ψ := originalPreparedState s₀ (0 : PhysicalData d) h UA Ub
    let y := WithLp.toLp 2 (Alignment.zeroAuxiliaryOutput (physicalSignalZero s₀) Ψ)
    let z := refinementAccepted (physicalMatrix A) κ ε y
    z ≠ 0 ∧ ‖NormedSpace.normalize z - physicalSolution A b‖ ≤ ε / 2 ∧
      1 / 65536 < ‖z‖ ^ 2 := by
  have hc := physical_original_preparation_coarse (activeIndex d) s₀ (0 : PhysicalData d)
    h A hA hunit hinv UA henc Ub b hb hcol hs
  dsimp only at hc ⊢
  obtain ⟨hsupport, hn, β, hβ0, hβ1, hPy, _⟩ := hc
  have hy := (zeroAuxiliaryOutput_norm_le (physicalSignalZero s₀)
    (originalPreparedState s₀ (0 : PhysicalData d) h UA Ub)).trans_eq hn
  have hAnorm : ‖A‖ ≤ 1 := by
    rw [← zeroExtend_norm (activeIndex d) A]
    exact norm_le_of_exact_block henc
  have hz := physical_refinement_component_guarantee (activeIndex d)
    A hA hunit hAnorm h.kappa_ge_two hinv hε0 hε1 b hb _ hy hsupport hβ0.le hβ1 hPy
  simpa only [physicalSolution, normalizedSolution,
    Perturbation.toEuclideanCLM_inverse A hunit] using hz

end OptimalQLS.PhysicalPadding
