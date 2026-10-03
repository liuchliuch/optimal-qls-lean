import OptimalQLS.KernelReflectionCircuit
import OptimalQLS.KernelReflectionNorms
import OptimalQLS.MatrixPseudoInverse
import OptimalQLS.SignalIsometry

/-! # Concrete kernel reflection with canonical spectral catalyst

The matrix, kernel projector, pseudoinverse and query instruction list are
all concrete. The elementary one/two-qubit work-gate synthesis remains a
separate obligation, so this module does not by itself claim all of 4.4.
-/
noncomputable section
namespace OptimalQLS
open Matrix
variable {S D B : Type*} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B]

/-- Exact implementation with the actual kernel and canonical pseudoinverse;
no kernel-product, catalyst, or compression identity is assumed. -/
theorem kernelReflection_exact (s₀ : S)
    (U : Matrix.unitaryGroup (S × D) ℂ) (hU : star (U : Matrix (S × D) (S × D) ℂ) = U)
    (H : Matrix D D ℂ) (hH : star H = H) {α τ : ℝ} (hα : 0 < α) (hτ : 0 < τ)
    (hblock : H = α • signalBlock s₀ U) (Ub : Matrix.unitaryGroup B ℂ) (ξ : D → ℂ) :
    let Q := signalProjector (D := D) s₀
    let p := signalInjection s₀ *ᵥ (matrixKernelProjection H *ᵥ ξ)
    let z := signalInjection s₀ *ᵥ (matrixPseudoInverse H hH *ᵥ ξ)
    ((kernelReflectionCircuit Q (signalProjector_star s₀) (signalProjector_idempotent s₀)
      (mul_pos hα hτ)).eval U Ub : Matrix (Fin 3 × (S × D)) (Fin 3 × (S × D)) ℂ) *ᵥ
      kernelTriple (signalInjection s₀ *ᵥ ξ)
        (kernelCatalystOne U (α * τ) α p z) (kernelCatalystTwo U (α * τ) α p z) =
      kernelTriple ((2 : ℝ) • p - signalInjection s₀ *ᵥ ξ)
        (kernelCatalystOne U (α * τ) α p z) (kernelCatalystTwo U (α * τ) α p z) := by
  dsimp only
  have hUU : (U : Matrix (S × D) (S × D) ℂ) * U = 1 := by
    simpa only [hU] using U.property.1
  obtain ⟨hp,hz⟩ := kernel_compression_from_encoding s₀ U H
    (matrixKernelProjection H) (matrixPseudoInverse H hH) hα.ne' hblock
    (matrix_mul_kernel H) (matrix_mul_pseudoInverse H hH) ξ
  exact kernelReflectionCircuit_restoration _ (signalProjector_star s₀)
    (signalProjector_idempotent s₀) U hUU Ub (mul_pos hα hτ) hα.ne' _ _ _
    (signalProjector_injection s₀ _) (signalProjector_injection s₀ _)
    (signalProjector_injection s₀ _) hp hz

/-- An orthogonal kernel projection has the literal orthogonality needed
for the catalyst's exact squared norm. -/
theorem matrixKernelProjection_orthogonal (H : Matrix D D ℂ) (ξ : EuclideanSpace ℂ D) :
    inner ℂ (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (matrixKernelProjection H) ξ)
      (ξ - Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (matrixKernelProjection H) ξ) = 0 := by
  simp only [matrixKernelProjection, StarAlgEquiv.apply_symm_apply]
  change inner ℂ ((LinearMap.ker (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H).toLinearMap).starProjection ξ)
    (ξ - (LinearMap.ker (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H).toLinearMap).starProjection ξ) = 0
  apply inner_eq_zero_symm.mp
  exact (LinearMap.ker (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H).toLinearMap).starProjection_inner_eq_zero ξ _
    ((LinearMap.ker (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H).toLinearMap).starProjection_apply_mem ξ)

/-- Exact catalyst costs for the actual encoding and canonical inverse.
Both component norms are derived; their sum is the query weight 4.4. -/
theorem kernelReflection_catalyst_norms (s₀ : S)
    (U : Matrix.unitaryGroup (S × D) ℂ) (hU : star (U : Matrix (S × D) (S × D) ℂ) = U)
    (H : Matrix D D ℂ) (hH : star H = H) {α τ : ℝ} (hα : 0 < α) (hτ : 0 < τ)
    (hblock : H = α • signalBlock s₀ U) (ξ : EuclideanSpace ℂ D) :
    let p := signalInjection s₀ *ᵥ (matrixKernelProjection H *ᵥ WithLp.ofLp ξ)
    let z := signalInjection s₀ *ᵥ (matrixPseudoInverse H hH *ᵥ WithLp.ofLp ξ)
    let weight := α * τ *
        ‖Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (matrixKernelProjection H) ξ‖ ^ 2 +
      α / τ * ‖Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (matrixPseudoInverse H hH) ξ‖ ^ 2
    ‖WithLp.toLp 2 (kernelCatalystOne U (α * τ) α p z)‖ ^ 2 = weight ∧
    ‖WithLp.toLp 2 (kernelCatalystTwo U (α * τ) α p z)‖ ^ 2 = weight := by
  let φ := Matrix.toEuclideanCLM (n := S × D) (𝕜 := ℂ)
  let ψ := Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)
  let J := signalIsometry (D := D) s₀
  let Q := φ (signalProjector (D := D) s₀)
  let V := φ U
  let p := J (ψ (matrixKernelProjection H) ξ)
  let z := J (ψ (matrixPseudoInverse H hH) ξ)
  have hp : Q p = p := by
    ext i
    exact congrFun (signalProjector_injection s₀ (matrixKernelProjection H *ᵥ WithLp.ofLp ξ)) i
  have hz : Q (V z) = α⁻¹ • (J ξ - p) := by
    ext i
    exact congrFun (kernel_compression_from_encoding s₀ U H (matrixKernelProjection H)
      (matrixPseudoInverse H hH) hα.ne' hblock (matrix_mul_kernel H)
      (matrix_mul_pseudoInverse H hH) (WithLp.ofLp ξ)).2 i
  have ho : inner ℂ p (J ξ - p) = 0 := by
    change inner ℂ (J (ψ (matrixKernelProjection H) ξ))
      (J ξ - J (ψ (matrixKernelProjection H) ξ)) = 0
    rw [← J.map_sub, J.inner_map_map]
    exact matrixKernelProjection_orthogonal H ξ
  obtain ⟨ho₁,ho₂⟩ := kernel_catalyst_orthogonal Q V
    (matrixHermitian_symmetric _ (signalProjector_star s₀))
    (matrixHermitian_symmetric _ hU) (J ξ) p z hp hz ho
  have hn : ∀ x, ‖V x‖ = ‖x‖ := by
    intro x
    exact ContinuousLinearMap.norm_map_of_mem_unitary (Unitary.map_mem φ U.property) x
  have h := kernel_catalyst_norms V hn p z ho₁ ho₂ hα hτ
  have hpn : ‖p‖ = ‖ψ (matrixKernelProjection H) ξ‖ := J.norm_map _
  have hzn : ‖z‖ = ‖ψ (matrixPseudoInverse H hH) ξ‖ := J.norm_map _
  rw [hpn, hzn] at h
  exact h

end OptimalQLS
