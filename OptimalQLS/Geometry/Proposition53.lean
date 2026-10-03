import OptimalQLS.Geometry.GeneralCorrection
import OptimalQLS.Geometry.SpectralPromises

noncomputable section
namespace OptimalQLS.Geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- The interval-union spectral premise in Proposition 5.3. -/
def PaperSpectralPromise (A : E →L[ℂ] E) (κ : ℝ) : Prop :=
  ∀ r : ℝ, (r : ℂ) ∈ spectrum ℂ A.toLinearMap →
    (-1 ≤ r ∧ r ≤ -κ⁻¹) ∨ (κ⁻¹ ≤ r ∧ r ≤ 1)

/-- The interval-union premise gives the norm-form spectral promise, using
Hermiticity to establish that the entire spectrum is real. -/
theorem norm_spectral_promise (A : E →L[ℂ] E) (hA : A.toLinearMap.IsSymmetric)
    {κ : ℝ} (hκ : 0 < κ) (hspec : PaperSpectralPromise A κ) :
    ∀ μ : ℂ, μ ∈ spectrum ℂ A.toLinearMap → κ⁻¹ ≤ ‖μ‖ ∧ ‖μ‖ ≤ 1 := by
  intro μ hμ
  have he : Module.End.HasEigenvalue A.toLinearMap μ :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ
  have hreal : (μ.re : ℂ) = μ := RCLike.conj_eq_iff_re.mp (hA.conj_eigenvalue_eq_self he)
  have h := hspec μ.re (by rwa [hreal])
  rw [← hreal, Complex.norm_real, Real.norm_eq_abs]
  have hi := inv_pos.mpr hκ
  rcases h with ⟨hl,hu⟩ | ⟨hl,hu⟩
  · rw [abs_of_nonpos (by linarith : μ.re ≤ 0)]
    constructor <;> linarith
  · rw [abs_of_nonneg (by linarith : 0 ≤ μ.re)]
    exact ⟨hl,hu⟩

/-- **Proposition 5.3**, from exactly the paper's Hermitian spectral
premise. The two operator inequalities are stated as their quadratic-form
definition, and the correction identity uses actual bounded operators and
actual inverses. Invertibility is also derived. -/
theorem proposition53 (A : E →L[ℂ] E) (hA : A.toLinearMap.IsSymmetric)
    {κ : ℝ} (hκ : 1 ≤ κ) (hspec : PaperSpectralPromise A κ) :
    IsUnit A ∧
    ((1 : E →L[ℂ] E) + ((κ⁻¹)^2 : ℂ) • (Ring.inverse A)^2) * A *
      Ring.inverse (A^2 + ((κ⁻¹)^2 : ℂ) • (1 : E →L[ℂ] E)) = Ring.inverse A ∧
    ∀ x : E,
      ‖x‖ ^ 2 ≤ (inner ℂ x (((1 : E →L[ℂ] E) + ((κ⁻¹)^2 : ℂ) • (Ring.inverse A)^2) x)).re ∧
      (inner ℂ x (((1 : E →L[ℂ] E) + ((κ⁻¹)^2 : ℂ) • (Ring.inverse A)^2) x)).re ≤
        2 * ‖x‖ ^ 2 := by
  have hκpos : 0 < κ := lt_of_lt_of_le (by norm_num) hκ
  obtain ⟨hunit, hAnorm, hinv⟩ := promises_from_spectrum A hA hκpos
    (norm_spectral_promise A hA hκpos hspec)
  exact ⟨hunit, proposition53_identity A hA hunit hκpos hAnorm hinv,
    proposition53_order A hA hunit hκpos hAnorm hinv⟩

end OptimalQLS.Geometry
