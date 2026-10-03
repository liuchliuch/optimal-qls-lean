import OptimalQLS.PhysicalPadding.Graph
import OptimalQLS.Preparation.OriginalState

/-! Actual accepted preparation states stay in the reducing active data range,
although the arbitrary supplied oracle can leak outside it off signal. -/
noncomputable section
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
namespace OptimalQLS.PhysicalPadding
open Matrix PolynomialTransform GraphEncoding Preparation Alignment TransducerCompiler
open scoped Matrix.Norms.L2Operator
variable {S D P : Type*} [Fintype S] [DecidableEq S]
  [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

/-- Support is derived from the already proved finite circuit Krylov invariant,
not imposed as an additional output promise or implemented by a data test. -/
theorem finitePreparedState_active (f : D ↪ P) (s₀ : S) {κ s ŝ α : ℝ}
    (h : BudgetParameters κ s ŝ) (hα : 0 < α)
    (A : Matrix D D ℂ) (hA : A.IsHermitian)
    (V : Matrix.unitaryGroup (S × (Fin 4 × P)) ℂ) (hV : star V.val = V.val)
    (Ub : Matrix.unitaryGroup (Fin 4 × P) ℂ) (i₀ : Fin 4 × P)
    (b : EuclideanSpace ℂ D) (hb : ‖b‖ = 1)
    (hcol : ∀ i, Ub i i₀ = graphInput (coordinateIsometry f b) i)
    (hblock : graphMatrix (zeroExtend f A) κ = α • signalBlock s₀ V) :
    ∃ x : EuclideanSpace ℂ (Fin 4 × D),
      WithLp.toLp 2 (zeroAuxiliaryOutput s₀
        (finitePreparedState s₀ h hα V Ub i₀ (WithLp.ofLp (graphInput (coordinateIsometry f b))))) =
      graphIsometry f x := by
  have he : ‖graphInput (coordinateIsometry f b)‖ = 1 := by
    rw [graphInput_norm, (coordinateIsometry f).norm_map, hb]
  have hm := finitePreparedState_zero_mem s₀ h hα V hV
    (graphMatrix (zeroExtend f A) κ) (graphMatrix_hermitian _ (zeroExtend_hermitian f A hA) κ)
    Ub i₀ (graphInput (coordinateIsometry f b)) he hcol hblock
  have hm' := (graphKrylov_active f A κ b) hm
  obtain ⟨x,hx⟩ := hm'
  exact ⟨x,hx.symm⟩

/-- Preparation from the very same physical UA and Ub has both the paper's
coarse guarantees and exact active support in the zero-auxiliary output. -/
theorem physical_original_preparation_coarse [Nonempty P] (f : D ↪ P)
    (s₀ : S) (i₀ : P) {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ)
    (A : Matrix D D ℂ) (hA : A.IsHermitian) (hunit : IsUnit A)
    (hinv : ‖Ring.inverse A‖ ≤ κ)
    (UA : Matrix.unitaryGroup (S × P) ℂ)
    (henc : IsBlockEncoding s₀ 1 0 UA (zeroExtend f A))
    (Ub : Matrix.unitaryGroup P ℂ) (b : EuclideanSpace ℂ D) (hb : ‖b‖ = 1)
    (hcol : ∀ i, Ub i i₀ = coordinateIsometry f b i)
    (hs : s = solutionScale 1 A b) :
    let Ψ := originalPreparedState s₀ i₀ h UA Ub
    let y := WithLp.toLp 2 (zeroAuxiliaryOutput (physicalSignalZero s₀) Ψ)
    let H := graphMatrix (zeroExtend f A) κ
    let u := normalizedProjectedInput H (graphInput (coordinateIsometry f b))
    (∃ x : EuclideanSpace ℂ (Fin 4 × D), y = graphIsometry f x) ∧
    ‖WithLp.toLp 2 Ψ‖ = 1 ∧ ∃ β : ℝ, 1/32 < β ∧ β ≤ 1 ∧
      kernelProjector H y = β • u ∧ kernelProjector H (y-β • u) = 0 := by
  have hα : 0 < 1+κ⁻¹ := by have := h.kappa_pos; positivity
  have hα2 : 1+κ⁻¹ ≤ 2 := by
    have hi : κ⁻¹ ≤ 1 := by
      rw [inv_eq_one_div]
      apply (div_le_iff₀ h.kappa_pos).mpr
      linarith [h.kappa_ge_two]
    linarith
  have hHA := zeroExtend_hermitian f A hA
  have hblock := exact_block_eq (physicalEncoding_exact κ h.kappa_pos s₀ UA _ hHA henc)
  have hInv : ‖Ring.inverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A)‖ ≤ κ := by
    rw [← Perturbation.toEuclideanCLM_inverse A hunit]
    exact hinv
  have hAnorm : ‖Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A‖ ≤ 1 := by
    have he := norm_le_of_exact_block henc
    have hlogical : ‖A‖ ≤ ‖zeroExtend f A‖ := by
      rw [← Matrix.l2_opNorm_toEuclideanCLM]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro x
      rw [← (coordinateIsometry f).norm_map]
      rw [← zeroExtend_apply]
      exact (Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) (zeroExtend f A)).le_opNorm _ |>.trans_eq
        (by rw [(coordinateIsometry f).norm_map]; rfl)
    exact hlogical.trans he
  have hp := physical_graphInput_promises f A hA
    (hunit.map (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)).toMonoidHom) h.kappa_pos hAnorm hInv b hb
  have hscale : ‖Ring.inverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) b‖ = s := by
    rw [← Perturbation.toEuclideanCLM_inverse A hunit]
    simpa only [solutionScale, one_mul] using hs.symm
  dsimp only at hp
  rw [hscale] at hp
  dsimp only
  rw [originalPreparedState_eq s₀ i₀ h UA Ub (coordinateIsometry f b) hcol]
  constructor
  · exact finitePreparedState_active f (physicalSignalZero s₀) h hα A hA
      (physicalEncoding κ h.kappa_pos UA) (physicalEncoding_hermitian κ h.kappa_pos UA)
      (signalLift (S := Fin 4) Ub) (1,i₀) b hb
      (graphInput_source Ub i₀ _ hcol) hblock
  · exact finite_preparation_coarse_component (physicalSignalZero s₀) h hα hα2
      (physicalEncoding κ h.kappa_pos UA) (physicalEncoding_hermitian κ h.kappa_pos UA)
      (graphMatrix (zeroExtend f A) κ) (graphMatrix_hermitian _ hHA κ)
      (signalLift (S := Fin 4) Ub) (1,i₀) (graphInput (coordinateIsometry f b)) hp.1
      (graphInput_source Ub i₀ _ hcol) hblock hp.2.1 hp.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2

end OptimalQLS.PhysicalPadding
