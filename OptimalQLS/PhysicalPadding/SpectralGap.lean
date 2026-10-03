import OptimalQLS.PhysicalPadding.Basis
import OptimalQLS.GraphEncoding.SpectralGap

/-!
# The physical graph gap without a global invertibility assumption

Zero-padding makes the data operator singular.  Nevertheless each nonzero
auxiliary eigenvalue has square aᵢ²+t², including aᵢ=0, so its modulus is at
least t.  This proves the normalized physical graph gap directly on the full
physical register, including all inactive data coordinates.
-/

noncomputable section
set_option synthInstance.maxSize 2048
namespace OptimalQLS.PhysicalPadding

open Matrix Geometry GraphEncoding
open scoped Matrix.Norms.L2Operator

/-- The auxiliary graph keeps a gap t even at a zero data eigenvalue. -/
theorem auxiliary_spectral_gap_singular_safe
    {ι : Type*} [Fintype ι] (a : ι → ℝ) {t : ℝ} (ht : 0 < t)
    (ha : ∀ i, |a i| ≤ 1) {μ : ℂ} (hμ : μ ≠ 0)
    (heig : Module.End.HasEigenvalue (auxiliary a t).toLinearMap μ) :
    t ≤ ‖μ‖ ∧ ‖μ‖ ≤ Real.sqrt (1 + t ^ 2) := by
  obtain ⟨x, hxmem, hxne⟩ := heig.exists_hasEigenvector
  have hx : auxiliary a t x = μ • x := Module.End.mem_eigenspace_iff.mp hxmem
  obtain ⟨i, hi⟩ := auxiliary_eigenvalue_square a t hμ hxne hx
  have hnorm : ‖μ‖ ^ 2 = a i ^ 2 + t ^ 2 := by
    have h := congrArg norm hi
    have hc : (a i : ℂ) ^ 2 + (t : ℂ) ^ 2 = ((a i ^ 2 + t ^ 2 : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hc, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (denominator_pos ht)] at h
    exact h
  have hai : a i ^ 2 ≤ 1 := by
    have h := (sq_le_sq₀ (abs_nonneg (a i)) (by norm_num : (0 : ℝ) ≤ 1)).mpr (ha i)
    simpa only [sq_abs, one_pow] using h
  constructor
  · apply (sq_le_sq₀ ht.le (norm_nonneg μ)).mp
    rw [hnorm]
    nlinarith [sq_nonneg (a i)]
  · apply (sq_le_sq₀ (norm_nonneg μ) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + t ^ 2), hnorm]
    linarith

/-- Original-coordinate auxiliary gap for an arbitrary Hermitian contraction,
with no lower bound on its data eigenvalues and no inverse. -/
theorem blockAuxiliary_spectral_gap_singular_safe
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (A : E →L[ℂ] E) (hA : A.toLinearMap.IsSymmetric) (hAnorm : ‖A‖ ≤ 1)
    {t : ℝ} (ht : 0 < t) {μ : ℂ} (hμ : μ ≠ 0)
    (heig : Module.End.HasEigenvalue (blockAuxiliary A t).toLinearMap μ) :
    t ≤ ‖μ‖ ∧ ‖μ‖ ≤ Real.sqrt (1 + t ^ 2) := by
  let U := (hA.eigenvectorBasis rfl).repr
  let a := hA.eigenvalues rfl
  have hdiag : ∀ x i, U (A x) i = (a i : ℂ) * U x i :=
    fun x i => hA.eigenvectorBasis_apply_self_apply rfl x i
  have ha : ∀ i, |a i| ≤ 1 := by
    intro i
    let v := hA.eigenvectorBasis rfl i
    have hv : ‖v‖ = 1 := (hA.eigenvectorBasis rfl).orthonormal.norm_eq_one i
    have he : A v = (a i : ℂ) • v :=
      Module.End.mem_eigenspace_iff.mp (hA.hasEigenvector_eigenvectorBasis rfl i).1
    have hn : ‖A v‖ = |a i| := by
      rw [he, norm_smul, hv, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hb := A.le_opNorm v
    rw [hv, mul_one, hn] at hb
    exact hb.trans hAnorm
  obtain ⟨x, hxmem, hxne⟩ := heig.exists_hasEigenvector
  have hx : blockAuxiliary A t x = μ • x := Module.End.mem_eigenspace_iff.mp hxmem
  have hy : auxiliary a t (tripleCoordinates U x) = μ • tripleCoordinates U x := by
    rw [← tripleCoordinates_intertwines U A a hdiag, hx, map_smul]
  have hyne : tripleCoordinates U x ≠ 0 := by simpa using hxne
  exact auxiliary_spectral_gap_singular_safe a ht ha hμ
    (Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hy, hyne⟩)

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The complete four-label graph has the singular-safe nonzero spectral gap. -/
theorem graphMatrix_spectral_gap_singular_safe
    (A : Matrix D D ℂ) (hA : A.IsHermitian) {κ : ℝ} (hκ : 0 < κ)
    (hAnorm : ‖A‖ ≤ 1) {μ : ℂ} (hμ : μ ≠ 0)
    (heig : Module.End.HasEigenvalue
      (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (graphMatrix A κ)).toLinearMap μ) :
    κ⁻¹ ≤ ‖μ‖ ∧ ‖μ‖ ≤ Real.sqrt (1 + (κ⁻¹) ^ 2) := by
  exact blockAuxiliary_spectral_gap_singular_safe
    (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) (matrixHermitian_symmetric A hA)
    hAnorm (inv_pos.mpr hκ) hμ (graphEigenvalue_active A κ hμ heig)

/-- The full normalized physical graph spectrum obeys the filter's exact gap,
even when its data operator is singular. -/
theorem normalized_graph_spectrum_singular_safe
    (A : Matrix D D ℂ) (hA : A.IsHermitian) {κ : ℝ} (hκ : 2 ≤ κ)
    (hAnorm : ‖A‖ ≤ 1) (μ : ℂ)
    (hmem : μ ∈ spectrum ℂ
      (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (normalizedGraph A κ)).toLinearMap)
    (hμ : μ ≠ 0) : 1 / (κ * (1 + κ⁻¹)) ≤ ‖μ‖ ∧ ‖μ‖ ≤ 1 := by
  have hk : 0 < κ := by linarith
  let α : ℝ := 1 + κ⁻¹
  have hα : 0 < α := by dsimp [α]; positivity
  have hαc : (α : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hα
  have heig := Module.End.hasEigenvalue_iff_mem_spectrum.mpr hmem
  obtain ⟨x, hxmem, hxne⟩ := heig.exists_hasEigenvector
  have hx : Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (normalizedGraph A κ) x =
      μ • x := Module.End.mem_eigenspace_iff.mp hxmem
  have hscale : Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (normalizedGraph A κ) =
      (α : ℂ)⁻¹ • Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (graphMatrix A κ) := by
    change Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ)
      ((α⁻¹ : ℝ) • graphMatrix A κ) = _
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
    simp
  rw [hscale] at hx
  change (α : ℂ)⁻¹ •
    (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (graphMatrix A κ) x) = μ • x at hx
  have hx' : Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (graphMatrix A κ) x =
      ((α : ℂ) * μ) • x := by
    calc
      _ = (α : ℂ) • ((α : ℂ)⁻¹ •
          (Matrix.toEuclideanCLM (n := Fin 4 × D) (𝕜 := ℂ) (graphMatrix A κ) x)) := by
        rw [smul_smul, mul_inv_cancel₀ hαc, one_smul]
      _ = (α : ℂ) • (μ • x) := by rw [hx]
      _ = _ := by rw [smul_smul]
  have hs := graphMatrix_spectral_gap_singular_safe A hA hk hAnorm (mul_ne_zero hαc hμ)
    (Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hx', hxne⟩)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα] at hs
  have hu : Real.sqrt (1 + (κ⁻¹) ^ 2) ≤ α := by
    have ht : 0 ≤ κ⁻¹ := (inv_pos.mpr hk).le
    have hsq := Real.sq_sqrt (show 0 ≤ 1 + (κ⁻¹) ^ 2 by positivity)
    have hnon := Real.sqrt_nonneg (1 + (κ⁻¹) ^ 2)
    dsimp [α] at *
    nlinarith
  constructor
  · change 1 / (κ * α) ≤ ‖μ‖
    have he : 1 / (κ * α) = κ⁻¹ / α := by
      simp [div_eq_mul_inv, _root_.mul_inv_rev, mul_comm]
    rw [he]
    exact (div_le_iff₀ hα).mpr (by simpa [mul_comm] using hs.1)
  · have hh := hs.2.trans hu
    nlinarith

/-- Applying the singular-safe theorem to the literal zero-extended data
matrix needs only the original matrix norm bound, never a padded inverse. -/
theorem physical_normalized_graph_spectrum_singular_safe
    {d : ℕ} [NeZero d] (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian)
    {κ : ℝ} (hκ : 2 ≤ κ) (hAnorm : ‖A‖ ≤ 1) (μ : ℂ)
    (hmem : μ ∈ spectrum ℂ
      (Matrix.toEuclideanCLM (n := Fin 4 × Fin (physicalDimension d)) (𝕜 := ℂ)
        (normalizedGraph (physicalMatrix A) κ)).toLinearMap)
    (hμ : μ ≠ 0) : 1 / (κ * (1 + κ⁻¹)) ≤ ‖μ‖ ∧ ‖μ‖ ≤ 1 := by
  apply normalized_graph_spectrum_singular_safe (physicalMatrix A)
    (zeroExtend_hermitian (activeIndex d) A hA) hκ _ μ hmem hμ
  rw [physicalMatrix, zeroExtend_norm]
  exact hAnorm

end OptimalQLS.PhysicalPadding
