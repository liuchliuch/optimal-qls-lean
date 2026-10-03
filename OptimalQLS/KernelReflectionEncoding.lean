import OptimalQLS.KernelReflection
import OptimalQLS.BlockEncoding

noncomputable section
namespace OptimalQLS
open Matrix
variable {S D : Type*} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]

/-- The actual computational signal projector in the shared workspace. -/
def signalProjector (s₀ : S) : Matrix (S × D) (S × D) ℂ :=
  signalInjection (D := D) s₀ * (signalInjection (D := D) s₀)ᴴ

theorem signalProjector_star (s₀ : S) : star (signalProjector (D := D) s₀) =
    signalProjector s₀ := by simp [signalProjector, Matrix.star_eq_conjTranspose]

theorem signalProjector_idempotent (s₀ : S) : signalProjector (D := D) s₀ *
    signalProjector s₀ = signalProjector s₀ := by
  simp only [signalProjector]
  calc
    _ = signalInjection s₀ * ((signalInjection s₀)ᴴ * signalInjection s₀) *
        (signalInjection s₀)ᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [signalInjection_isometry, Matrix.mul_one]

theorem signalProjector_injection (s₀ : S) (x : D → ℂ) :
    signalProjector s₀ *ᵥ (signalInjection s₀ *ᵥ x) = signalInjection s₀ *ᵥ x := by
  simp only [signalProjector, Matrix.mulVec_mulVec]
  rw [Matrix.mul_assoc, signalInjection_isometry, Matrix.mul_one]

/-- A block encoding's full-workspace compression is derived from its
literal signal block, including the normalization factor. -/
theorem signalProjector_oracle_injection (s₀ : S)
    (U : Matrix.unitaryGroup (S × D) ℂ) (H : Matrix D D ℂ)
    {α : ℝ} (hα : α ≠ 0) (hblock : H = α • signalBlock s₀ U)
    (x : D → ℂ) :
    signalProjector s₀ *ᵥ ((U : Matrix (S × D) (S × D) ℂ) *ᵥ
      (signalInjection s₀ *ᵥ x)) =
      α⁻¹ • (signalInjection s₀ *ᵥ (H *ᵥ x)) := by
  rw [hblock]
  simp only [signalProjector, signalBlock, Matrix.mulVec_mulVec,
    Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]
  rw [inv_mul_cancel₀ hα, one_smul]
  simp only [Matrix.mul_assoc]

/-- All compression premises of the explicit catalyst theorem follow from
an actual exact block encoding and the Moore–Penrose/kernel identities. -/
theorem kernel_compression_from_encoding (s₀ : S)
    (U : Matrix.unitaryGroup (S × D) ℂ) (H P Z : Matrix D D ℂ)
    {α : ℝ} (hα : α ≠ 0) (hblock : H = α • signalBlock s₀ U)
    (hHP : H * P = 0) (hHZ : H * Z = 1 - P) (ξ : D → ℂ) :
    signalProjector s₀ *ᵥ ((U : Matrix (S × D) (S × D) ℂ) *ᵥ
      (signalInjection s₀ *ᵥ (P *ᵥ ξ))) = 0 ∧
    signalProjector s₀ *ᵥ ((U : Matrix (S × D) (S × D) ℂ) *ᵥ
      (signalInjection s₀ *ᵥ (Z *ᵥ ξ))) =
      α⁻¹ • ((signalInjection s₀ *ᵥ ξ) - (signalInjection s₀ *ᵥ (P *ᵥ ξ))) := by
  constructor
  · rw [signalProjector_oracle_injection s₀ U H hα hblock,
      Matrix.mulVec_mulVec ξ H P, hHP, Matrix.zero_mulVec, Matrix.mulVec_zero, smul_zero]
  · rw [signalProjector_oracle_injection s₀ U H hα hblock,
      Matrix.mulVec_mulVec ξ H Z, hHZ, Matrix.sub_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_sub]

/-- Exact restoration specialized to a literal Hermitian block encoding.
The public and private vectors are fully specified, not existential
catalyst certificates. -/
theorem kernel_encoding_restoration (s₀ : S)
    (U : Matrix.unitaryGroup (S × D) ℂ) (hU : star (U : Matrix (S × D) (S × D) ℂ) = U)
    (H P Z : Matrix D D ℂ) {α τ : ℝ} (hα : 0 < α) (hτ : 0 < τ)
    (hblock : H = α • signalBlock s₀ U)
    (hHP : H * P = 0) (hHZ : H * Z = 1 - P) (ξ : D → ℂ) :
    let Q := signalProjector (D := D) s₀
    let p := signalInjection s₀ *ᵥ (P *ᵥ ξ)
    let z := signalInjection s₀ *ᵥ (Z *ᵥ ξ)
    (kernelWorkUnitary Q (signalProjector_star s₀) (signalProjector_idempotent s₀)
      (kernelMixA (α * τ)) (kernelMixB (α * τ))
      (kernelMix_normalized (mul_pos hα hτ)) :
      Matrix (Fin 3 × (S × D)) (Fin 3 × (S × D)) ℂ) *ᵥ
      kernelTriple (signalInjection s₀ *ᵥ ξ)
        ((U : Matrix (S × D) (S × D) ℂ) *ᵥ kernelCatalystOne U (α * τ) α p z)
        ((U : Matrix (S × D) (S × D) ℂ) *ᵥ kernelCatalystTwo U (α * τ) α p z) =
      kernelTriple ((2 : ℝ) • p - signalInjection s₀ *ᵥ ξ)
        (kernelCatalystOne U (α * τ) α p z) (kernelCatalystTwo U (α * τ) α p z) := by
  dsimp only
  have hUU : (U : Matrix (S × D) (S × D) ℂ) * U = 1 := by
    simpa only [hU] using U.property.1
  obtain ⟨hp,hz⟩ := kernel_compression_from_encoding s₀ U H P Z hα.ne' hblock hHP hHZ ξ
  exact kernel_catalyst_restoration _ _ (signalProjector_star s₀)
    (signalProjector_idempotent s₀) hUU (mul_pos hα hτ) hα.ne' _ _ _
    (signalProjector_injection s₀ ξ) (signalProjector_injection s₀ (P *ᵥ ξ))
    (signalProjector_injection s₀ (Z *ᵥ ξ)) hp hz

end OptimalQLS
