import OptimalQLS.Alignment.EncodedInvariant

noncomputable section
namespace OptimalQLS.Alignment
open Matrix
variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Exact kernel projection, in the Hilbert-space convention used by the paper. -/
def kernelProjector (H : Matrix D D ℂ) : EuclideanSpace ℂ D →L[ℂ] EuclideanSpace ℂ D :=
  (LinearMap.ker (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H).toLinearMap).starProjection

def normalizedProjectedInput (H : Matrix D D ℂ) (e : EuclideanSpace ℂ D) : EuclideanSpace ℂ D :=
  ‖kernelProjector H e‖⁻¹ • kernelProjector H e

theorem kernelProjector_mul (H : Matrix D D ℂ) (hH : star H=H) :
    kernelProjector H * Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H = 0 := by
  have h := congrArg star (hermitian_mul_kernel (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H))
  have hP : star (kernelProjector H)=kernelProjector H :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (LinearMap.ker (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H).toLinearMap).starProjection_isSymmetric
  have hHerm : star (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H)=
      Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H := by rw [← map_star,hH]
  rw [StarMul.star_mul,star_zero] at h
  change star (kernelProjector H) * star (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H)=0 at h
  simpa only [hHerm,hP] using h

/-- No approximation appears here: every real Krylov output has an exactly
real kernel component, even if the projected input vanishes. -/
theorem dataKrylov_exact_alignment (H : Matrix D D ℂ) (hH : star H=H)
    (e : EuclideanSpace ℂ D) {y : D → ℂ} (hy : y ∈ dataKrylov H (WithLp.ofLp e)) :
    ∃ β : ℝ, kernelProjector H (WithLp.toLp 2 y) = β • normalizedProjectedInput H e := by
  let T := Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H
  have hPH : (kernelProjector H).toLinearMap.restrictScalars ℝ *
      T.toLinearMap.restrictScalars ℝ = 0 := by
    apply LinearMap.ext
    intro x
    exact congrArg (fun A : EuclideanSpace ℂ D →L[ℂ] EuclideanSpace ℂ D => A x)
      (kernelProjector_mul H hH)
  obtain ⟨c,hc⟩ := projection_realKrylov_collinear
    ((kernelProjector H).toLinearMap.restrictScalars ℝ) (T.toLinearMap.restrictScalars ℝ)
    hPH e hy
  change kernelProjector H (WithLp.toLp 2 y) = c • kernelProjector H e at hc
  refine ⟨c*‖kernelProjector H e‖, ?_⟩
  rw [hc,normalizedProjectedInput,smul_smul]
  by_cases hz : ‖kernelProjector H e‖=0
  · have hez : kernelProjector H e=0 := norm_eq_zero.mp hz
    simp [hez]
  · rw [mul_assoc,mul_inv_cancel₀ hz,mul_one]

end OptimalQLS.Alignment
