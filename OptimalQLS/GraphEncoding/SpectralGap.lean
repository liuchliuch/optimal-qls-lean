import OptimalQLS.GraphEncoding.Geometry

/-! # The normalized physical graph gap, from the original matrix promises -/
noncomputable section
set_option synthInstance.maxSize 1024
namespace OptimalQLS.GraphEncoding
open Matrix Geometry
open scoped Matrix.Norms.L2Operator
variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Every nonzero physical graph eigenvalue already occurs on the active triple. -/
theorem graphEigenvalue_active (A : Matrix D D ℂ) (κ : ℝ) {μ : ℂ} (hμ : μ ≠ 0)
    (heig : Module.End.HasEigenvalue
      (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (graphMatrix A κ)).toLinearMap μ) :
    Module.End.HasEigenvalue
      (blockAuxiliary (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) κ⁻¹).toLinearMap μ := by
  obtain ⟨x,hxmem,hxne⟩ := heig.exists_hasEigenvector
  have hx : Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (graphMatrix A κ) x = μ • x :=
    Module.End.mem_eigenspace_iff.mp hxmem
  have h3 (d : D) : x (3,d) = 0 := by
    have h := congrArg (fun y : EuclideanSpace ℂ (Fin 4 × D) => y (3,d)) hx
    have hz : (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (graphMatrix A κ) x) (3,d) = 0 := by
      simp [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct]
    dsimp only at h
    rw [hz] at h
    change 0 = μ * x (3,d) at h
    exact (mul_eq_zero.mp h.symm).resolve_left hμ
  have hn : activeRestriction x ≠ 0 := by
    intro hz
    apply hxne
    ext ⟨g,d⟩
    fin_cases g
    · have h := congrArg (fun y : Block (EuclideanSpace ℂ D) => y 0 d) hz
      simpa [activeRestriction] using h
    · have h := congrArg (fun y : Block (EuclideanSpace ℂ D) => y 1 d) hz
      simpa [activeRestriction] using h
    · have h := congrArg (fun y : Block (EuclideanSpace ℂ D) => y 2 d) hz
      simpa [activeRestriction] using h
    · simpa using h3 d
  apply Module.End.hasEigenvalue_of_hasEigenvector
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hn⟩
  change blockAuxiliary (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) κ⁻¹ (activeRestriction x) = μ • activeRestriction x
  rw [← activeRestriction_intertwines, hx, map_smul]

theorem graphMatrix_spectral_gap (A : Matrix D D ℂ) (hA : A.IsHermitian)
    (hunit : IsUnit A) {κ : ℝ} (hκ : 0 < κ) (hAnorm : ‖A‖ ≤ 1)
    (hinorm : ‖Ring.inverse A‖ ≤ κ) {μ : ℂ} (hμ : μ ≠ 0)
    (heig : Module.End.HasEigenvalue
      (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (graphMatrix A κ)).toLinearMap μ) :
    Real.sqrt 2 / κ ≤ ‖μ‖ ∧ ‖μ‖ ≤ Real.sqrt (1+(κ⁻¹)^2) := by
  let φ := Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)
  have hi : ‖Ring.inverse (φ A)‖ ≤ κ := by
    rw [← Perturbation.toEuclideanCLM_inverse A hunit]
    exact hinorm
  exact lemma42_spectral_gap (φ A) (matrixHermitian_symmetric A hA)
    (hunit.map φ.toMonoidHom) hκ hAnorm hi hμ (graphEigenvalue_active A κ hμ heig)

/-- Normalization appearing in Proposition4.3. -/
def normalizedGraph (A : Matrix D D ℂ) (κ : ℝ) : Matrix (Fin 4 × D) (Fin 4 × D) ℂ :=
  ((1+κ⁻¹)⁻¹ : ℝ) • graphMatrix A κ

theorem normalizedGraph_hermitian (A : Matrix D D ℂ) (hA : A.IsHermitian) (κ : ℝ) :
    (normalizedGraph A κ).IsHermitian := by
  change (((1+κ⁻¹)⁻¹ : ℝ) • graphMatrix A κ)ᴴ = _
  rw [Matrix.conjTranspose_smul]
  exact congrArg (fun M : Matrix (Fin 4 × D) (Fin 4 × D) ℂ => ((1+κ⁻¹)⁻¹ : ℝ) • M)
    (graphMatrix_hermitian A hA κ)

/-- The exact scalar gap required by the Chebyshev kernel filter, with no
assumed physical spectral promise. -/
theorem normalizedGraph_spectrum (A : Matrix D D ℂ) (hA : A.IsHermitian)
    (hunit : IsUnit A) {κ : ℝ} (hκ : 2 ≤ κ) (hAnorm : ‖A‖ ≤ 1)
    (hinorm : ‖Ring.inverse A‖ ≤ κ) (μ : ℂ)
    (hmem : μ ∈ spectrum ℂ
      (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (normalizedGraph A κ)).toLinearMap)
    (hμ : μ ≠ 0) : 1/(2*κ) ≤ ‖μ‖ ∧ ‖μ‖ ≤ 1 := by
  have hk : 0 < κ := by linarith
  let α : ℝ := 1+κ⁻¹
  have hα : 0 < α := by dsimp [α]; positivity
  have hαc : (α : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hα
  have heig := Module.End.hasEigenvalue_iff_mem_spectrum.mpr hmem
  obtain ⟨x,hxmem,hxne⟩ := heig.exists_hasEigenvector
  have hx : Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (normalizedGraph A κ) x = μ • x :=
    Module.End.mem_eigenspace_iff.mp hxmem
  have hscale : Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (normalizedGraph A κ) =
      (α : ℂ)⁻¹ • Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (graphMatrix A κ) := by
    change Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) ((α⁻¹ : ℝ) • graphMatrix A κ) = _
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
    simp
  rw [hscale] at hx
  change (α : ℂ)⁻¹ • (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (graphMatrix A κ) x) = μ • x at hx
  have hx' : Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (graphMatrix A κ) x =
      ((α : ℂ)*μ) • x := by
    calc
      _ = (α : ℂ) • ((α : ℂ)⁻¹ •
          (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (graphMatrix A κ) x)) := by
        rw [smul_smul, mul_inv_cancel₀ hαc, one_smul]
      _ = (α : ℂ) • (μ • x) := by rw [hx]
      _ = _ := by rw [smul_smul]
  have hs := graphMatrix_spectral_gap A hA hunit hk hAnorm hinorm (mul_ne_zero hαc hμ)
    (Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hx',hxne⟩)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα] at hs
  have ht0 : 0 ≤ κ⁻¹ := (inv_pos.mpr hk).le
  have ht1 : κ⁻¹ ≤ 1 := (inv_le_one₀ hk).mpr (by linarith)
  have hα2 : α ≤ 2 := by dsimp [α]; linarith
  have hsqrt : 1 ≤ Real.sqrt 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2), Real.sqrt_nonneg (2:ℝ)]
  have hl : κ⁻¹ ≤ α*‖μ‖ := by
    have hh : κ⁻¹ ≤ Real.sqrt 2 / κ := by rw [div_eq_mul_inv]; nlinarith
    exact hh.trans hs.1
  have hl' : κ⁻¹ ≤ 2*‖μ‖ := hl.trans (mul_le_mul_of_nonneg_right hα2 (norm_nonneg _))
  have hu : Real.sqrt (1+(κ⁻¹)^2) ≤ α := by
    have hsq := Real.sq_sqrt (show 0 ≤ 1+(κ⁻¹)^2 by positivity)
    have hnon := Real.sqrt_nonneg (1+(κ⁻¹)^2)
    dsimp [α] at *
    nlinarith
  constructor
  · rw [div_eq_mul_inv, _root_.mul_inv_rev]
    norm_num
    nlinarith
  · have hh := hs.2.trans hu
    nlinarith

/-- The sharper normalized lower bound used literally by the paper’s filter gap. -/
theorem normalizedGraph_spectrum_paper (A : Matrix D D ℂ) (hA : A.IsHermitian)
    (hunit : IsUnit A) {κ : ℝ} (hκ : 2 ≤ κ) (hAnorm : ‖A‖ ≤ 1)
    (hinorm : ‖Ring.inverse A‖ ≤ κ) (μ : ℂ)
    (hmem : μ ∈ spectrum ℂ
      (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (normalizedGraph A κ)).toLinearMap)
    (hμ : μ ≠ 0) : 1/(κ*(1+κ⁻¹)) ≤ ‖μ‖ ∧ ‖μ‖ ≤ 1 := by
  have hk : 0 < κ := by linarith
  let α : ℝ := 1+κ⁻¹
  have hα : 0 < α := by dsimp [α]; positivity
  have hαc : (α : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hα
  have heig := Module.End.hasEigenvalue_iff_mem_spectrum.mpr hmem
  obtain ⟨x,hxmem,hxne⟩ := heig.exists_hasEigenvector
  have hx : Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (normalizedGraph A κ) x = μ • x :=
    Module.End.mem_eigenspace_iff.mp hxmem
  have hscale : Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (normalizedGraph A κ) =
      (α : ℂ)⁻¹ • Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (graphMatrix A κ) := by
    change Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) ((α⁻¹ : ℝ) • graphMatrix A κ) = _
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
    simp
  rw [hscale] at hx
  change (α : ℂ)⁻¹ • (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (graphMatrix A κ) x) = μ • x at hx
  have hx' : Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (graphMatrix A κ) x =
      ((α : ℂ)*μ) • x := by
    calc
      _ = (α : ℂ) • ((α : ℂ)⁻¹ •
          (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (graphMatrix A κ) x)) := by
        rw [smul_smul, mul_inv_cancel₀ hαc, one_smul]
      _ = (α : ℂ) • (μ • x) := by rw [hx]
      _ = _ := by rw [smul_smul]
  have hs := graphMatrix_spectral_gap A hA hunit hk hAnorm hinorm (mul_ne_zero hαc hμ)
    (Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hx',hxne⟩)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα] at hs
  have ht0 : 0 ≤ κ⁻¹ := (inv_pos.mpr hk).le
  have ht1 : κ⁻¹ ≤ 1 := (inv_le_one₀ hk).mpr (by linarith)
  have hα2 : α ≤ 2 := by dsimp [α]; linarith
  have hsqrt : 1 ≤ Real.sqrt 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2), Real.sqrt_nonneg (2:ℝ)]
  have hl : κ⁻¹ ≤ α*‖μ‖ := by
    have hh : κ⁻¹ ≤ Real.sqrt 2 / κ := by rw [div_eq_mul_inv]; nlinarith
    exact hh.trans hs.1
  have hl' : κ⁻¹ ≤ 2*‖μ‖ := hl.trans (mul_le_mul_of_nonneg_right hα2 (norm_nonneg _))
  have hu : Real.sqrt (1+(κ⁻¹)^2) ≤ α := by
    have hsq := Real.sq_sqrt (show 0 ≤ 1+(κ⁻¹)^2 by positivity)
    have hnon := Real.sqrt_nonneg (1+(κ⁻¹)^2)
    dsimp [α] at *
    nlinarith
  constructor
  · change 1/(κ*α) ≤ ‖μ‖
    have he : 1/(κ*α) = κ⁻¹/α := by simp [div_eq_mul_inv, _root_.mul_inv_rev, mul_comm]
    rw [he]
    exact (div_le_iff₀ hα).mpr (by simpa [mul_comm] using hl)
  · have hh := hs.2.trans hu
    nlinarith

end OptimalQLS.GraphEncoding
