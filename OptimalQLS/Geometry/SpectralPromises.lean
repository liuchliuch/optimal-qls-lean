import OptimalQLS.Geometry.Resolvent

noncomputable section
namespace OptimalQLS.Geometry
variable {ι : Type*} [Fintype ι]

/-- The operator norm here is the L2-induced operator norm. -/
theorem diagonal_real_opNorm_le (f : ι → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ i, |f i| ≤ M) : ‖diagonal (fun i => (f i : ℂ))‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mp
  rw [diagonal_real_norm_sq]
  calc
    ∑ i, f i ^ 2 * ‖x i‖ ^ 2 ≤ ∑ i, M ^ 2 * ‖x i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have h := hf i
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (f i)) hM).mpr h
    _ = (M * ‖x‖) ^ 2 := by
      rw [← Finset.mul_sum, ← EuclideanSpace.norm_sq_eq, mul_pow]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Unitary conjugation preserves an operator-norm upper bound. -/
theorem conjugate_opNorm_le (U : E ≃ₗᵢ[ℂ] Vec ι) (T : Vec ι →L[ℂ] Vec ι)
    {M : ℝ} (hM : 0 ≤ M) (hT : ‖T‖ ≤ M) : ‖conjugate U T‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro x
  simp only [conjugate_apply, LinearIsometryEquiv.norm_map]
  calc
    ‖T (U x)‖ ≤ ‖T‖ * ‖U x‖ := T.le_opNorm _
    _ ≤ M * ‖x‖ := by rw [U.norm_map]; exact mul_le_mul_of_nonneg_right hT (norm_nonneg _)

/-- The paper's spectral premise implies all operator-norm promises and
invertibility; no inverse-norm conclusion needs to be postulated. -/
theorem promises_from_spectrum (A : E →L[ℂ] E) (hA : A.toLinearMap.IsSymmetric)
    {κ : ℝ} (hκ : 0 < κ)
    (hspec : ∀ μ : ℂ, μ ∈ spectrum ℂ A.toLinearMap → κ⁻¹ ≤ ‖μ‖ ∧ ‖μ‖ ≤ 1) :
    IsUnit A ∧ ‖A‖ ≤ 1 ∧ ‖Ring.inverse A‖ ≤ κ := by
  let U := (hA.eigenvectorBasis rfl).repr
  let a := hA.eigenvalues rfl
  have hdiag : ∀ x i, U (A x) i = (a i : ℂ) * U x i :=
    fun x i => hA.eigenvectorBasis_apply_self_apply rfl x i
  have ha : ∀ i, κ⁻¹ ≤ |a i| ∧ |a i| ≤ 1 := by
    intro i
    have he := Module.End.hasEigenvalue_of_hasEigenvector
      (hA.hasEigenvector_eigenvectorBasis rfl i)
    have h := hspec _ he.mem_spectrum
    simpa [Complex.norm_real, Real.norm_eq_abs] using h
  have hane : ∀ i, a i ≠ 0 := by
    intro i hi
    have h := (ha i).1
    rw [hi, abs_zero] at h
    exact (not_le_of_gt (inv_pos.mpr hκ)) h
  obtain ⟨hunit,hinv⟩ := inverse_from_coordinates U A a hdiag hane
  refine ⟨hunit, ?_, ?_⟩
  · rw [operator_eq_conjugate U A a hdiag]
    apply conjugate_opNorm_le U _ (by norm_num)
    exact diagonal_real_opNorm_le a (by norm_num) (fun i => (ha i).2)
  · rw [hinv]
    apply conjugate_opNorm_le U _ hκ.le
    have hcast : (fun i => ((a i)⁻¹ : ℂ)) = fun i => (((a i)⁻¹ : ℝ) : ℂ) := by ext; simp
    rw [hcast]
    apply diagonal_real_opNorm_le _ hκ.le
    intro i
    rw [abs_inv, inv_eq_one_div]
    apply (div_le_iff₀ (abs_pos.mpr (hane i))).mpr
    have h := (ha i).1
    rw [inv_eq_one_div] at h
    have h' := (div_le_iff₀ hκ).mp h
    simpa [mul_comm] using h'

end OptimalQLS.Geometry
