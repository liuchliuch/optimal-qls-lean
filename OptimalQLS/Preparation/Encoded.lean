import OptimalQLS.Preparation.Ideal

/-! # Concrete preparation transduction from actual encoded matrix promises -/
noncomputable section
namespace OptimalQLS.Preparation
open Matrix
variable {S D : Type*} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]

def encodedPreparationCircuit (s₀ : S) {α τ r : ℝ} (hα : 0<α) (hτ : 0<τ) (hr : |r|<1) :
    QueryCircuit (S × D) (S × D) (Fin 8 × (S × D)) :=
  preparationCircuit (signalProjector s₀) (signalProjector_star s₀)
    (signalProjector_idempotent s₀) (mul_pos hα hτ) hr

/-- The full five-component catalyst identity is proved from the literal
block encoding and canonical kernel/pseudoinverse. No restoration or query
certificate is an input. -/
theorem encodedPreparation_transduction (s₀ : S)
    (V : Matrix.unitaryGroup (S × D) ℂ) (hV : star (V : Matrix (S × D) (S × D) ℂ)=V)
    (H : Matrix D D ℂ) (hH : star H=H) (R : Matrix.unitaryGroup D ℂ)
    {α τ r : ℝ} (hα : 0<α) (hτ : 0<τ) (hr : |r|<1)
    (hblock : H=α • signalBlock s₀ V) (ξ : D → ℂ) :
    let U := idealUnitary H R
    let qD := fractionalCatalyst U r ξ
    let ψD := fractionalAction U r*ᵥξ
    let q := signalInjection s₀*ᵥqD
    let p := signalInjection s₀*ᵥ(matrixKernelProjection H*ᵥqD)
    let z := signalInjection s₀*ᵥ(matrixPseudoInverse H hH*ᵥqD)
    let ω₁ := kernelCatalystOne V (α*τ) α p z
    let ω₂ := kernelCatalystTwo V (α*τ) α p z
    ((encodedPreparationCircuit (D := D) s₀ hα hτ hr).eval V (signalLift (S := S) R) :
      Matrix (Fin 8 × (S × D)) (Fin 8 × (S × D)) ℂ)*ᵥ
      bundle8 (signalInjection s₀*ᵥξ) q ω₁ ω₂ ((2:ℝ) • p-q) =
      bundle8 (signalInjection s₀*ᵥψD) q ω₁ ω₂ ((2:ℝ) • p-q) := by
  let U := idealUnitary H R
  let qD := fractionalCatalyst U r ξ
  let ψD := fractionalAction U r*ᵥξ
  let J := signalInjection (D := D) s₀
  have hUU : (V : Matrix (S × D) (S × D) ℂ)*(V : Matrix (S × D) (S × D) ℂ)=1 := by
    simpa only [hV] using V.property.1
  have hUq : J*ᵥ((U : Matrix D D ℂ)*ᵥqD) =
      -((signalLift (S := S) R : Matrix (S × D) (S × D) ℂ)*ᵥ
        ((2:ℝ) • (J*ᵥ(matrixKernelProjection H*ᵥqD))-J*ᵥqD)) := by
    rw [idealUnitary_apply,Matrix.mulVec_neg,← signalLift_injection s₀ R,
      Matrix.mulVec_sub,Matrix.mulVec_smul]
  obtain ⟨ha,hb⟩ := fractional_rows U hr ξ
  have hfirst := congrArg (fun v : D → ℂ => J*ᵥv) ha
  have hsecond := congrArg (fun v : D → ℂ => J*ᵥv) hb
  simp only [Matrix.mulVec_add,Matrix.mulVec_smul] at hfirst hsecond
  change (-r) • (J*ᵥξ)+Real.sqrt (1-r^2) • (J*ᵥ((U : Matrix D D ℂ)*ᵥqD)) = J*ᵥψD at hfirst
  change Real.sqrt (1-r^2) • (J*ᵥξ)+r • (J*ᵥ((U : Matrix D D ℂ)*ᵥqD)) = J*ᵥqD at hsecond
  rw [hUq] at hfirst hsecond
  obtain ⟨hVp,hVz⟩ := kernel_compression_from_encoding s₀ V H (matrixKernelProjection H)
    (matrixPseudoInverse H hH) hα.ne' hblock (matrix_mul_kernel H)
    (matrix_mul_pseudoInverse H hH) qD
  dsimp only
  exact preparationCircuit_restoration _ V (signalLift (S := S) R)
    (signalProjector_star s₀) (signalProjector_idempotent s₀) hUU
    (mul_pos hα hτ) hα.ne' hr _ _ _ _ _
    (signalProjector_injection s₀ qD)
    (signalProjector_injection s₀ (matrixKernelProjection H*ᵥqD))
    (signalProjector_injection s₀ (matrixPseudoInverse H hH*ᵥqD)) hVp hVz hfirst hsecond

/-- Both intermediate oracles are genuinely separate and each is called once. -/
theorem encodedPreparation_counts (s₀ : S) {α τ r : ℝ}
    (hα : 0<α) (hτ : 0<τ) (hr : |r|<1) :
    (encodedPreparationCircuit (D := D) s₀ hα hτ hr).matrixQueries=1 ∧
    (encodedPreparationCircuit (D := D) s₀ hα hτ hr).vectorQueries=1 :=
  preparationCircuit_counts _ _ _ _ _

end OptimalQLS.Preparation
