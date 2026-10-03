import OptimalQLS.Geometry.Resolvent

noncomputable section
namespace OptimalQLS.Geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- The canonical Moore–Penrose inverse constructed from the spectral theorem.
Its defining four equations were proved in `original_moore_penrose`. -/
def auxiliaryPseudoInverse (A : E →L[ℂ] E) (hA : A.toLinearMap.IsSymmetric) (t : ℝ) :
    Block E →L[ℂ] Block E :=
  conjugate (tripleCoordinates (hA.eigenvectorBasis rfl).repr)
    (pseudoInverse (hA.eigenvalues rfl) t)

/-- Lemma 4.2: the exact two displayed formulas in the original coordinates. -/
theorem lemma42_exact_formulas (A : E →L[ℂ] E) (hA : A.toLinearMap.IsSymmetric)
    {κ : ℝ} (hκ : 0 < κ) (b : E) :
    let D := A ^ 2 + ((κ⁻¹)^2 : ℂ) • (1 : E →L[ℂ] E)
    let e := blockTriple 0 b 0
    let P := (LinearMap.ker (blockAuxiliary A κ⁻¹).toLinearMap).starProjection
    P e = blockTriple 0 (((κ⁻¹)^2 : ℂ) • Ring.inverse D b)
      ((κ⁻¹ : ℂ) • A (Ring.inverse D b)) ∧
    auxiliaryPseudoInverse A hA κ⁻¹ e = blockTriple (A (Ring.inverse D b)) 0 0 := by
  dsimp only
  constructor
  · simpa only [Complex.ofReal_inv] using
      original_projection_input (hA.eigenvectorBasis rfl).repr A (hA.eigenvalues rfl)
        (fun x i => hA.eigenvectorBasis_apply_self_apply rfl x i) (inv_pos.mpr hκ) b
  · exact original_pseudoInverse_input (hA.eigenvectorBasis rfl).repr A (hA.eigenvalues rfl)
        (fun x i => hA.eigenvectorBasis_apply_self_apply rfl x i) (inv_pos.mpr hκ) b

/-- Lemma 4.2: all projection-weight estimates, from the original promises. -/
theorem lemma42_projection_bounds (A : E →L[ℂ] E) (hA : A.toLinearMap.IsSymmetric)
    (hunit : IsUnit A) {κ : ℝ} (hκ : 0 < κ)
    (hAnorm : ‖A‖ ≤ 1) (hinorm : ‖Ring.inverse A‖ ≤ κ) (b : E) (hb : ‖b‖ = 1) :
    let s := ‖Ring.inverse A b‖
    let P := (LinearMap.ker (blockAuxiliary A κ⁻¹).toLinearMap).starProjection
    let γsq := ‖P (blockTriple 0 b 0)‖ ^ 2
    s ^ 2 / (2 * κ ^ 2) ≤ γsq ∧ γsq ≤ s ^ 2 / κ ^ 2 ∧
      0 < γsq ∧ γsq ≤ 1 / 2 := by
  let U := (hA.eigenvectorBasis rfl).repr
  let a := hA.eigenvalues rfl
  have hdiag : ∀ x i, U (A x) i = (a i : ℂ) * U x i :=
    fun x i => hA.eigenvectorBasis_apply_self_apply rfl x i
  have ha : ∀ i, κ⁻¹ ≤ |a i| := fun i =>
    (spectral_coordinate_bounds A hA hunit hκ hAnorm hinorm i).1
  have hane : ∀ i, a i ≠ 0 := by
    intro i hi
    have h := ha i
    rw [hi, abs_zero] at h
    exact (not_le_of_gt (inv_pos.mpr hκ)) h
  have hinv := (inverse_from_coordinates U A a hdiag hane).2
  dsimp only
  rw [original_kernel_projection U A a hdiag (inv_pos.mpr hκ), hinv]
  simp only [conjugate_apply, LinearIsometryEquiv.norm_map,
    tripleCoordinates_blockTriple, map_zero]
  exact lemma42_diagonal_norms a hκ ha (U b) (by simpa using hb)

/-- Lemma 4.2: pseudoinverse solution-vector norm estimate. -/
theorem lemma42_pseudoinverse_bound (A : E →L[ℂ] E) (hA : A.toLinearMap.IsSymmetric)
    (hunit : IsUnit A) {κ : ℝ} (hκ : 0 < κ)
    (hAnorm : ‖A‖ ≤ 1) (hinorm : ‖Ring.inverse A‖ ≤ κ) (b : E) :
    ‖auxiliaryPseudoInverse A hA κ⁻¹ (blockTriple 0 b 0)‖ ≤ ‖Ring.inverse A b‖ := by
  let U := (hA.eigenvectorBasis rfl).repr
  let a := hA.eigenvalues rfl
  have hdiag : ∀ x i, U (A x) i = (a i : ℂ) * U x i :=
    fun x i => hA.eigenvectorBasis_apply_self_apply rfl x i
  have ha : ∀ i, κ⁻¹ ≤ |a i| := fun i =>
    (spectral_coordinate_bounds A hA hunit hκ hAnorm hinorm i).1
  have hane : ∀ i, a i ≠ 0 := by
    intro i hi
    have h := ha i
    rw [hi, abs_zero] at h
    exact (not_le_of_gt (inv_pos.mpr hκ)) h
  rw [(inverse_from_coordinates U A a hdiag hane).2]
  change ‖conjugate (tripleCoordinates U) (pseudoInverse a κ⁻¹) (blockTriple 0 b 0)‖ ≤ _
  simp only [conjugate_apply, LinearIsometryEquiv.norm_map,
    tripleCoordinates_blockTriple, map_zero]
  exact pseudoInverse_input_norm_le a (inv_pos.mpr hκ) ha (U b)

/-- Lemma 4.2: H⁺ kills the normalized kernel vector. -/
theorem lemma42_pseudoinverse_normalized_kernel (A : E →L[ℂ] E)
    (hA : A.toLinearMap.IsSymmetric) {κ : ℝ} (hκ : 0 < κ) (b : E) :
    let P := (LinearMap.ker (blockAuxiliary A κ⁻¹).toLinearMap).starProjection
    auxiliaryPseudoInverse A hA κ⁻¹
      (NormedSpace.normalize (P (blockTriple 0 b 0))) = 0 := by
  let U := (hA.eigenvectorBasis rfl).repr
  let a := hA.eigenvalues rfl
  have hdiag : ∀ x i, U (A x) i = (a i : ℂ) * U x i :=
    fun x i => hA.eigenvectorBasis_apply_self_apply rfl x i
  dsimp only
  rw [original_kernel_projection U A a hdiag (inv_pos.mpr hκ)]
  change conjugate (tripleCoordinates U) (pseudoInverse a κ⁻¹)
    (NormedSpace.normalize (conjugate (tripleCoordinates U) (kernelProjector a κ⁻¹)
      (blockTriple 0 b 0))) = 0
  rw [NormedSpace.normalize]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
  have hprod : conjugate (tripleCoordinates U) (pseudoInverse a κ⁻¹) *
      conjugate (tripleCoordinates U) (kernelProjector a κ⁻¹) = 0 := by
    rw [← map_mul, pseudoInverse_mul_projector, map_zero]
  have h := congrArg (fun T : Block E →L[ℂ] Block E => T (blockTriple 0 b 0)) hprod
  have hzero : conjugate (tripleCoordinates U) (pseudoInverse a κ⁻¹)
      (conjugate (tripleCoordinates U) (kernelProjector a κ⁻¹) (blockTriple 0 b 0)) = 0 := by
    simpa using h
  simp only [hzero, smul_zero]

/-- Lemma 4.2: full spectral gap of the actual original-coordinate auxiliary matrix. -/
theorem lemma42_spectral_gap (A : E →L[ℂ] E) (hA : A.toLinearMap.IsSymmetric)
    (hunit : IsUnit A) {κ : ℝ} (hκ : 0 < κ)
    (hAnorm : ‖A‖ ≤ 1) (hinorm : ‖Ring.inverse A‖ ≤ κ) {μ : ℂ} (hμ : μ ≠ 0)
    (heig : Module.End.HasEigenvalue (blockAuxiliary A κ⁻¹).toLinearMap μ) :
    Real.sqrt 2 / κ ≤ ‖μ‖ ∧ ‖μ‖ ≤ Real.sqrt (1 + (κ⁻¹)^2) := by
  let U := (hA.eigenvectorBasis rfl).repr
  let a := hA.eigenvalues rfl
  have hdiag : ∀ x i, U (A x) i = (a i : ℂ) * U x i :=
    fun x i => hA.eigenvectorBasis_apply_self_apply rfl x i
  have ha : ∀ i, κ⁻¹ ≤ |a i| ∧ |a i| ≤ 1 := fun i =>
    spectral_coordinate_bounds A hA hunit hκ hAnorm hinorm i
  obtain ⟨x, hxmem, hxne⟩ := heig.exists_hasEigenvector
  have hx : blockAuxiliary A κ⁻¹ x = μ • x := Module.End.mem_eigenspace_iff.mp hxmem
  have hy : auxiliary a κ⁻¹ (tripleCoordinates U x) = μ • (tripleCoordinates U x) := by
    rw [← tripleCoordinates_intertwines U A a hdiag, hx, map_smul]
  have hyne : tripleCoordinates U x ≠ 0 := by simpa using hxne
  have hh : Module.End.HasEigenvalue (auxiliary a κ⁻¹).toLinearMap μ :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hy, hyne⟩
  simpa [div_eq_mul_inv] using auxiliary_spectral_gap a (inv_pos.mpr hκ) ha hμ hh

/-- The original-coordinate auxiliary matrix is Hermitian. -/
theorem lemma42_auxiliary_hermitian (A : E →L[ℂ] E) (hA : A.toLinearMap.IsSymmetric)
    (t : ℝ) : (blockAuxiliary A t).toLinearMap.IsSymmetric := by
  rw [blockAuxiliary_eq_conjugate (hA.eigenvectorBasis rfl).repr A (hA.eigenvalues rfl)
    (fun x i => hA.eigenvectorBasis_apply_self_apply rfl x i)]
  exact conjugate_symmetric _ _ (auxiliary_symmetric _ _)

/-- The named pseudoinverse satisfies all four Moore–Penrose equations. -/
theorem lemma42_moore_penrose (A : E →L[ℂ] E) (hA : A.toLinearMap.IsSymmetric)
    {κ : ℝ} (hκ : 0 < κ) :
    let H := blockAuxiliary A κ⁻¹
    let Q := auxiliaryPseudoInverse A hA κ⁻¹
    H * Q * H = H ∧ Q * H * Q = Q ∧
      (H * Q).toLinearMap.IsSymmetric ∧ (Q * H).toLinearMap.IsSymmetric := by
  exact original_moore_penrose (hA.eigenvectorBasis rfl).repr A (hA.eigenvalues rfl)
    (fun x i => hA.eigenvectorBasis_apply_self_apply rfl x i) (inv_pos.mpr hκ)

end OptimalQLS.Geometry
