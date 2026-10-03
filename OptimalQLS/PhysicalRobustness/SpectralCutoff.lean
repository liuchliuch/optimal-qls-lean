import OptimalQLS.HermitianPseudoInverse

/-! Actual finite spectral cutoffs, not supplied inverse/projector certificates. -/
noncomputable section
namespace OptimalQLS.PhysicalRobustness
open Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Orthogonal low-spectral projection of the actual noisy physical operator. -/
def lowProjector (B : E →L[ℂ] E) (hB : B.toLinearMap.IsSymmetric) (δ : ℝ) : E →L[ℂ] E :=
  conjugate (hB.eigenvectorBasis rfl).repr
    (diagonal (fun i => if |hB.eigenvalues rfl i| ≤ δ then (1 : ℂ) else 0))

/-- The actual inverse on the high spectral subspace, zero on the low subspace. -/
def highInverse (B : E →L[ℂ] E) (hB : B.toLinearMap.IsSymmetric) (δ : ℝ) : E →L[ℂ] E :=
  conjugate (hB.eigenvectorBasis rfl).repr
    (diagonal (fun i => if |hB.eigenvalues rfl i| ≤ δ then (0 : ℂ)
      else ((hB.eigenvalues rfl i)⁻¹ : ℝ)))

theorem lowProjector_idempotent (B : E →L[ℂ] E) (hB : B.toLinearMap.IsSymmetric) (δ : ℝ) :
    lowProjector B hB δ * lowProjector B hB δ = lowProjector B hB δ := by
  unfold lowProjector
  rw [← map_mul]
  congr 1
  ext x i
  by_cases hi : |hB.eigenvalues rfl i| ≤ δ <;> simp [hi]

theorem lowProjector_symmetric (B : E →L[ℂ] E) (hB : B.toLinearMap.IsSymmetric) (δ : ℝ) :
    (lowProjector B hB δ).toLinearMap.IsSymmetric := by
  apply conjugate_symmetric
  convert diagonal_real_symmetric (fun i => if |hB.eigenvalues rfl i| ≤ δ then 1 else 0) using 1
  ext x i
  by_cases hi : |hB.eigenvalues rfl i| ≤ δ <;> simp [hi]

theorem lowProjector_norm_le_one (B : E →L[ℂ] E) (hB : B.toLinearMap.IsSymmetric) (δ : ℝ) :
    ‖lowProjector B hB δ‖ ≤ 1 := by
  apply conjugate_opNorm_le _ _ zero_le_one
  convert diagonal_real_opNorm_le
    (fun i => if |hB.eigenvalues rfl i| ≤ δ then 1 else 0) zero_le_one (by
      intro i; by_cases hi : |hB.eigenvalues rfl i| ≤ δ <;> simp [hi]) using 1
  congr 1
  ext x i
  by_cases hi : |hB.eigenvalues rfl i| ≤ δ <;> simp [hi]

theorem lowProjector_commutes (B : E →L[ℂ] E) (hB : B.toLinearMap.IsSymmetric) (δ : ℝ) :
    lowProjector B hB δ * B = B * lowProjector B hB δ := by
  conv_lhs => rhs; rw [operator_eq_conjugate (hB.eigenvectorBasis rfl).repr B
    (hB.eigenvalues rfl) (fun x i => hB.eigenvectorBasis_apply_self_apply rfl x i)]
  conv_rhs => lhs; rw [operator_eq_conjugate (hB.eigenvectorBasis rfl).repr B
    (hB.eigenvalues rfl) (fun x i => hB.eigenvectorBasis_apply_self_apply rfl x i)]
  unfold lowProjector
  rw [← map_mul, ← map_mul]
  congr 1
  ext x i
  simp only [ContinuousLinearMap.mul_apply, diagonal_apply]
  ring

theorem lowPart_norm (B : E →L[ℂ] E) (hB : B.toLinearMap.IsSymmetric)
    {δ : ℝ} (hδ : 0 ≤ δ) : ‖B * lowProjector B hB δ‖ ≤ δ := by
  conv_lhs => arg 1; lhs; rw [operator_eq_conjugate (hB.eigenvectorBasis rfl).repr B
    (hB.eigenvalues rfl) (fun x i => hB.eigenvectorBasis_apply_self_apply rfl x i)]
  unfold lowProjector
  rw [← map_mul]
  have heq : diagonal (fun i => (hB.eigenvalues rfl i : ℂ)) *
      diagonal (fun i => if |hB.eigenvalues rfl i| ≤ δ then (1 : ℂ) else 0) =
      diagonal (fun i => ((if |hB.eigenvalues rfl i| ≤ δ then hB.eigenvalues rfl i else 0 : ℝ) : ℂ)) := by
    ext x i
    by_cases hi : |hB.eigenvalues rfl i| ≤ δ <;> simp [hi]
  rw [heq]
  apply conjugate_opNorm_le _ _ hδ
  apply diagonal_real_opNorm_le _ hδ
  intro i
  split_ifs with hi
  · exact hi
  · simpa using hδ

theorem highInverse_mul_self (B : E →L[ℂ] E) (hB : B.toLinearMap.IsSymmetric)
    {δ : ℝ} (hδ : 0 ≤ δ) : highInverse B hB δ * B = 1-lowProjector B hB δ := by
  conv_lhs => rhs; rw [operator_eq_conjugate (hB.eigenvectorBasis rfl).repr B
    (hB.eigenvalues rfl) (fun x i => hB.eigenvectorBasis_apply_self_apply rfl x i)]
  unfold highInverse lowProjector
  rw [← map_mul, ← map_one (conjugate (hB.eigenvectorBasis rfl).repr), ← map_sub]
  congr 1
  ext x i
  by_cases hi : |hB.eigenvalues rfl i| ≤ δ
  · simp [hi]
  · have hn : hB.eigenvalues rfl i ≠ 0 := by intro hz; simp [hz, hδ] at hi
    have hnc : (hB.eigenvalues rfl i : ℂ) ≠ 0 := by exact_mod_cast hn
    simp [hi, mul_assoc, hnc]

theorem lowProjector_mul_highInverse (B : E →L[ℂ] E)
    (hB : B.toLinearMap.IsSymmetric) (δ : ℝ) :
    lowProjector B hB δ * highInverse B hB δ = 0 := by
  unfold lowProjector highInverse
  rw [← map_mul, ← map_zero (conjugate (hB.eigenvectorBasis rfl).repr)]
  congr 1
  ext x i
  by_cases hi : |hB.eigenvalues rfl i| ≤ δ <;> simp [hi]

/-- The gap used here will be obtained from the original support and the
absolute perturbation bound; the cutoff and inverse themselves are concrete. -/
theorem highInverse_norm (B : E →L[ℂ] E) (hB : B.toLinearMap.IsSymmetric)
    {δ g : ℝ} (hg : 0 < g)
    (hgap : ∀ i, |hB.eigenvalues rfl i| ≤ δ ∨ g ≤ |hB.eigenvalues rfl i|) :
    ‖highInverse B hB δ‖ ≤ g⁻¹ := by
  apply conjugate_opNorm_le _ _ (inv_nonneg.mpr hg.le)
  convert diagonal_real_opNorm_le
    (fun i => if |hB.eigenvalues rfl i| ≤ δ then 0 else (hB.eigenvalues rfl i)⁻¹)
    (inv_nonneg.mpr hg.le) (by
      intro i
      by_cases hi : |hB.eigenvalues rfl i| ≤ δ
      · simpa [hi] using inv_nonneg.mpr hg.le
      · simp only [hi, if_false, abs_inv]
        exact inv_anti₀ hg ((hgap i).resolve_left hi)) using 1
  congr 1
  ext x i
  by_cases hi : |hB.eigenvalues rfl i| ≤ δ <;> simp [hi]

end OptimalQLS.PhysicalRobustness
