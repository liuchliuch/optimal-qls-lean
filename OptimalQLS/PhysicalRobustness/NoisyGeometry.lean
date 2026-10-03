import OptimalQLS.PhysicalRobustness.ResolventGraph
import OptimalQLS.PhysicalRobustness.PreparationScale

/-! Complete noisy graph promises derived from the original logical problem.
The original norm bound is a separate hypothesis, as in Theorem 7.2; it is
never inferred from an approximate block encoding. -/
noncomputable section
namespace OptimalQLS.PhysicalRobustness
open Geometry PhysicalPadding GraphEncoding Preparation TransducerCompiler Matrix
open scoped Matrix.Norms.L2Operator

section Abstract
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- The noisy graph retains the half-overlap hypothesis of the existing
finite preparation theorem, with explicit slack 1/20. -/
theorem noisy_regularized_overlap_upper (J : E →ₗᵢ[ℂ] F)
    (A : E →L[ℂ] E) (hA : A.toLinearMap.IsSymmetric) (hunit : IsUnit A)
    (H B : F →L[ℂ] F) (hB : B.toLinearMap.IsSymmetric)
    (hHJ : ∀ x, H (J x)=J (A x))
    {κ t δ : ℝ} (hκ : 0 ≤ κ) (ht : 0 < t) (hδ : 0 ≤ δ)
    (hkt : κ*t=1/2) (hdt : δ/t ≤ 1/2)
    (hinv : ‖Ring.inverse A‖ ≤ κ) (hpert : ‖B-H‖ ≤ δ)
    (b : E) (hb : ‖b‖=1) :
    t^2*‖Ring.inverse (imaginaryShift B t) (J b)‖^2 ≤ 9/20 := by
  let u := Ring.inverse (imaginaryShift A t) b
  let v := Ring.inverse (imaginaryShift B t) (J b)
  have he := noisy_regularized_solution_error J A hA H B hB hHJ ht hδ hpert b
  have hn := norm_sub_norm_le v (J u)
  rw [J.norm_map] at hn
  have hm := mul_le_mul_of_nonneg_right hdt (norm_nonneg u)
  have hv : ‖v‖ ≤ (3/2)*‖u‖ := by change ‖v-J u‖ ≤ (δ/t)*‖u‖ at he; linarith
  have hv2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hv
  have hgap := regularized_solution_gap_bound A hA hunit hκ ht hinv b
  rw [hb] at hgap
  have hkt2 : κ^2*t^2=1/4 := by nlinarith [congrArg (fun r : ℝ => r^2) hkt]
  rw [hkt2] at hgap
  have hgm := mul_le_mul_of_nonneg_left hgap (sq_nonneg t)
  have hvm := mul_le_mul_of_nonneg_left hv2 (sq_nonneg t)
  change t^2*‖v‖^2 ≤ _
  change (1+1/4)*‖u‖^2 ≤ κ^2*1^2 at hgap
  nlinarith [hkt2]
end Abstract

section Matrices
variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

/-- All geometric and scalar hypotheses of the existing finite preparation
are proved for arbitrary noisy full-register B, including off-support mixing. -/
theorem noisy_graph_promises (f : D ↪ P)
    (A : Matrix D D ℂ) (hA : A.IsHermitian) (hunit : IsUnit A)
    (hAnorm : ‖A‖ ≤ 1) (B : Matrix P P ℂ) (hB : B.IsHermitian) (hBnorm : ‖B‖ ≤ 1)
    (b : EuclideanSpace ℂ D) (hb : ‖b‖=1)
    {κ δ ŝ : ℝ} (hκ : 2 ≤ κ) (hδ : 0 ≤ δ)
    (hinv : ‖Ring.inverse A‖ ≤ κ) (hpert : ‖B-zeroExtend f A‖ ≤ δ)
    (hsmall : κ*δ ≤ 1/4)
    (hestlo : solutionScale 1 A b/2 ≤ ŝ) (hesthi : ŝ ≤ 2*solutionScale 1 A b) :
    let C := Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) B
    let w := ‖Ring.inverse (imaginaryShift C (2*κ)⁻¹) (coordinateIsometry f b)‖
    let s := noisyAnalysisScale w ŝ
    let H := graphMatrix B (2*κ)
    let e := graphInput (coordinateIsometry f b)
    let Q := (LinearMap.ker (Matrix.toEuclideanCLM (n := Fin 4 × P) (𝕜 := ℂ) H).toLinearMap).starProjection
    BudgetParameters (2*κ) s (9*ŝ/8) ∧
      ‖e‖=1 ∧ s^2/(2*(2*κ)^2)≤‖Q e‖^2 ∧ ‖Q e‖^2≤s^2/(2*κ)^2 ∧
      ‖Q e‖^2≤1/2 ∧
      ‖Matrix.toEuclideanCLM (n := Fin 4 × P) (𝕜 := ℂ)
        (matrixPseudoInverse H (graphMatrix_hermitian B hB (2*κ))) e‖≤s ∧
      2*solutionScale 1 A b/3 ≤ s := by
  let J := coordinateIsometry f
  let R := restriction f
  let T := Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A
  let Z := Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) (zeroExtend f A)
  let C := Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) B
  let t := (2*κ)⁻¹
  let v := Ring.inverse (imaginaryShift C t) (J b)
  let w := ‖v‖
  let s₀ := ‖Ring.inverse T b‖
  let s := noisyAnalysisScale w ŝ
  have hk : 0 < κ := by linarith
  have hT : T.toLinearMap.IsSymmetric := matrixHermitian_symmetric A hA
  have hC : C.toLinearMap.IsSymmetric := matrixHermitian_symmetric B hB
  have hTu : IsUnit T := hunit.map (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)).toMonoidHom
  have hTi : ‖Ring.inverse T‖ ≤ κ := by rw [← Perturbation.toEuclideanCLM_inverse A hunit]; exact hinv
  have hCZ : ‖C-Z‖ ≤ δ := by
    change ‖Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) B-
      Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) (zeroExtend f A)‖ ≤ δ
    rw [← map_sub]
    exact hpert
  have ht : 0 < t := by dsimp [t]; positivity
  have hkt : κ*t=1/2 := by dsimp [t]; field_simp
  have hdt : δ/t ≤ 1/2 := by dsimp [t]; rw [div_inv_eq_mul]; nlinarith
  have ht1 : t ≤ 1 := by
    dsimp [t]
    rw [inv_le_one₀ (by positivity : (0:ℝ)<2*κ)]
    linarith
  have hsEq : solutionScale 1 A b=s₀ := by
    simp only [solutionScale, one_mul]
    rw [Perturbation.toEuclideanCLM_inverse A hunit]
  have hs0 : 1 ≤ s₀ := by
    have he := Perturbation.apply_inverse T hTu b
    have hn := T.le_opNorm (Ring.inverse T b)
    rw [he, hb] at hn
    have htN : ‖T‖ ≤ 1 := hAnorm
    have hm := mul_le_mul_of_nonneg_right htN (norm_nonneg (Ring.inverse T b))
    dsimp [s₀]
    nlinarith
  have hsκ : s₀ ≤ κ := by
    have hn := (Ring.inverse T).le_opNorm b
    rw [hb, mul_one] at hn
    exact hn.trans hTi
  have hwl : 2*s₀/3 ≤ w := noisy_regularized_solution_lower J R
    (restriction_isometry f) (restriction_norm_le f) T hT hTu Z C hC
    (zeroExtend_restrict f A) hk.le ht hδ hkt.le hsmall hTi hCZ b
  have hwu : w ≤ 3*s₀/2 := noisy_regularized_solution_upper J T hT hTu Z C hC
    (zeroExtend_apply f A) hk.le ht hδ hdt hTi hCZ b
  have hbn : ‖J b‖=1 := (J.norm_map b).trans hb
  have hwunit : 1 ≤ 2*w^2 := regularized_solution_unit_lower C hC hBnorm ht ht1 (J b) hbn
  have hscale := noisyAnalysisScale_bounds (κ := κ) (s := s₀) (ŝ := ŝ) (w := w) hκ hs0 hsκ
    (by rwa [hsEq] at hestlo) (by rwa [hsEq] at hesthi) (norm_nonneg v) hwl hwu hwunit
  have hhalf := noisy_regularized_overlap_upper J T hT hTu Z C hC
    (zeroExtend_apply f A) hk.le ht hδ hkt hdt hTi hCZ b hb
  have hproj : ‖(LinearMap.ker (Matrix.toEuclideanCLM (n := Fin 4 × P) (𝕜 := ℂ)
      (graphMatrix B (2*κ))).toLinearMap).starProjection (graphInput (J b))‖^2 = t^2*w^2 := by
    rw [graphInput_active, activeTriple_kernel_projection, activeTriple.norm_map,
      blockGraph_projection_norm_sq C hC ht]
  have hMP : ‖Matrix.toEuclideanCLM (n := Fin 4 × P) (𝕜 := ℂ)
      (matrixPseudoInverse (graphMatrix B (2*κ)) (graphMatrix_hermitian B hB (2*κ)))
      (graphInput (J b))‖ ≤ w := by
    rw [graphInput_active, activeTriple_matrix_pseudoInverse B hB (by positivity : 0<2*κ),
      activeTriple.norm_map]
    exact blockGraph_pseudoInverse_norm_le C hC ht (J b)
  dsimp only
  refine ⟨hscale.1,by rw [graphInput_norm, J.norm_map, hb],?_,?_,?_,hMP.trans hscale.2.1,?_⟩
  · rw [hproj]
    change s^2/(2*(2*κ)^2) ≤ t^2*w^2
    have hh := hscale.2.2.1
    dsimp only [t]
    rw [inv_pow]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*(2*κ)^2)).mpr
    have hn : (2*κ)^2 ≠ 0 := by positivity
    field_simp
    nlinarith
  · rw [hproj]
    have hs2 := (sq_le_sq₀ (norm_nonneg v) (by dsimp [s,noisyAnalysisScale]; positivity)).mpr hscale.2.1
    dsimp only [t]
    rw [inv_pow, div_eq_mul_inv]
    change ((2*κ)^2)⁻¹*w^2 ≤ s^2*((2*κ)^2)⁻¹
    calc
      _ ≤ ((2*κ)^2)⁻¹*s^2 := mul_le_mul_of_nonneg_left hs2 (by positivity)
      _ = _ := by ring
  · rw [hproj]
    linarith
  · simpa only [hsEq] using hscale.2.2.2
end Matrices

end OptimalQLS.PhysicalRobustness
