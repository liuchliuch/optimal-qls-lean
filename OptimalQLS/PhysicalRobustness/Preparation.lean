import OptimalQLS.PhysicalRobustness.NoisyGeometry
import OptimalQLS.Preparation.OriginalState

/-! The actual finite preparation circuit on arbitrary noisy physical input.
Only classical κ and the supplied estimate select its code; the regularized
scale below is confined to its proof, by uniform_in_scale. -/
noncomputable section
namespace OptimalQLS.PhysicalRobustness
open Geometry PhysicalPadding GraphEncoding Preparation TransducerCompiler Alignment Matrix
open scoped Matrix.Norms.L2Operator
set_option synthInstance.maxSize 4096

variable {D P S : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]
  [Fintype S] [DecidableEq S] [Nonempty P]

/-- Fixed approximation is viewed as the exact actual block B. The preparation
remains the already constructed original-oracle circuit, with κ multiplied by
2 and the supplied estimate multiplied by 9/8. -/
theorem noisy_original_preparation_coarse (f : D ↪ P) (s₀ : S) (i₀ : P)
    (A : Matrix D D ℂ) (hA : A.IsHermitian) (hunit : IsUnit A) (hAnorm : ‖A‖≤1)
    (B : Matrix P P ℂ) (hB : B.IsHermitian)
    (UA : Matrix.unitaryGroup (S × P) ℂ) (henc : IsBlockEncoding s₀ 1 0 UA B)
    (Ub : Matrix.unitaryGroup P ℂ) (b : EuclideanSpace ℂ D) (hb : ‖b‖=1)
    (hcol : ∀ i, Ub i i₀=coordinateIsometry f b i)
    {κ δ ŝ : ℝ} (hκ : 2≤κ) (hδ : 0≤δ) (hinv : ‖Ring.inverse A‖≤κ)
    (hpert : ‖B-zeroExtend f A‖≤δ) (hsmall : κ*δ≤1/4)
    (hestlo : solutionScale 1 A b/2≤ŝ) (hesthi : ŝ≤2*solutionScale 1 A b) :
    let C := Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) B
    let w := ‖Ring.inverse (imaginaryShift C (2*κ)⁻¹) (coordinateIsometry f b)‖
    ∃ h : BudgetParameters (2*κ) (noisyAnalysisScale w ŝ) (9*ŝ/8),
      let Ψ := originalPreparedState s₀ i₀ h UA Ub
      let y := WithLp.toLp 2 (zeroAuxiliaryOutput (physicalSignalZero s₀) Ψ)
      let H := graphMatrix B (2*κ)
      let u := normalizedProjectedInput H (graphInput (coordinateIsometry f b))
      ‖WithLp.toLp 2 Ψ‖=1 ∧ ∃ β : ℝ, 1/32<β ∧ β≤1 ∧
        kernelProjector H y=β • u ∧ kernelProjector H (y-β • u)=0 := by
  have hp := noisy_graph_promises f A hA hunit hAnorm B hB (norm_le_of_exact_block henc)
    b hb hκ hδ hinv hpert hsmall hestlo hesthi
  dsimp only at hp ⊢
  let h := hp.1
  refine ⟨h,?_⟩
  have hk : 0<2*κ := by linarith
  have hα : 0<1+(2*κ)⁻¹ := by positivity
  have hα2 : 1+(2*κ)⁻¹≤2 := by
    have hi : (2*κ)⁻¹≤1 := (inv_le_one₀ hk).mpr (by linarith)
    linarith
  have hblock := exact_block_eq (physicalEncoding_exact (2*κ) hk s₀ UA B hB henc)
  rw [originalPreparedState_eq s₀ i₀ h UA Ub (coordinateIsometry f b) hcol]
  exact finite_preparation_coarse_component (physicalSignalZero s₀) h hα hα2
    (physicalEncoding (2*κ) hk UA) (physicalEncoding_hermitian (2*κ) hk UA)
    (graphMatrix B (2*κ)) (graphMatrix_hermitian B hB (2*κ))
    (signalLift (S := Fin 4) Ub) (1,i₀) (graphInput (coordinateIsometry f b)) hp.2.1
    (graphInput_source Ub i₀ (coordinateIsometry f b) hcol) hblock
    hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2.1

end OptimalQLS.PhysicalRobustness
