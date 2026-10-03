import OptimalQLS.Preparation.OriginalQueries
import OptimalQLS.Preparation.Coarse

noncomputable section
namespace OptimalQLS.Preparation
open Matrix TransducerCompiler GraphEncoding Alignment
open scoped Matrix.Norms.L2Operator
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000
variable {S D : Type*} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]

/-- A fixed computational-basis input, with graph label01. Preparing that
known label costs one X gate and makes no oracle call. -/
def preparationBasisInput (s₀ : S) (i₀ : D) {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ) :
    SynthSpace (PreparationData S D) (preparationExponent κ) → ℂ :=
  synthInput h.layout (preparationInternal (physicalSignalZero s₀)
    (signalInjection (1 : Fin 4)*ᵥPi.single i₀ 1))

def originalPreparedState (s₀ : S) (i₀ : D) {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ)
    (UA : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup D ℂ) :
    SynthSpace (PreparationData S D) (preparationExponent κ) → ℂ :=
  ((originalPreparationAlgorithm s₀ i₀ h).eval UA Ub).val*ᵥpreparationBasisInput s₀ i₀ h

/-- The prepared state is obtained from the original U_b, with its initial
query included, and equals the state used by the finite error/alignment proof. -/
theorem originalPreparedState_eq (s₀ : S) (i₀ : D) {κ s ŝ : ℝ}
    (h : BudgetParameters κ s ŝ) (UA : Matrix.unitaryGroup (S × D) ℂ)
    (Ub : Matrix.unitaryGroup D ℂ) (b : EuclideanSpace ℂ D) (hcol : ∀ i,Ub i i₀=b i) :
    originalPreparedState s₀ i₀ h UA Ub=
      finitePreparedState (physicalSignalZero s₀) h
        (by have := h.kappa_pos; positivity : 0<1+κ⁻¹)
        (physicalEncoding κ h.kappa_pos UA) (signalLift (S := Fin 4) Ub)
        (1,i₀) (WithLp.ofLp (graphInput b)) := by
  have hUb : Ub.val*ᵥPi.single i₀ 1=WithLp.ofLp b := by
    ext i
    simpa only [Matrix.mulVec_single_one] using hcol i
  simp only [originalPreparedState,originalPreparationAlgorithm,QueryCircuit.eval_append,
    QueryCircuit.eval,QueryInstruction.eval,Bool.false_eq_true,ite_false,one_mul,
    Submonoid.coe_mul,← Matrix.mulVec_mulVec,preparationBasisInput]
  rw [preparationSourcePort_input,hUb,originalPreparationCircuit_eval]
  rfl

/-- All amplitude, normalization, and exact real-alignment guarantees follow
from the original Hermitian problem instance and the supplied relaxed estimate. -/
theorem original_preparation_coarse [Nonempty D] (s₀ : S) (i₀ : D) {κ s ŝ : ℝ}
    (h : BudgetParameters κ s ŝ) (A : Matrix D D ℂ) (hA : A.IsHermitian)
    (hunit : IsUnit A) (hinv : ‖Ring.inverse A‖≤κ)
    (UA : Matrix.unitaryGroup (S × D) ℂ) (henc : IsBlockEncoding s₀ 1 0 UA A)
    (Ub : Matrix.unitaryGroup D ℂ) (b : EuclideanSpace ℂ D) (hb : ‖b‖=1)
    (hcol : ∀ i,Ub i i₀=b i) (hs : s=solutionScale 1 A b) :
    let Ψ := originalPreparedState s₀ i₀ h UA Ub
    let y := WithLp.toLp 2 (zeroAuxiliaryOutput (physicalSignalZero s₀) Ψ)
    let H := graphMatrix A κ
    let u := normalizedProjectedInput H (graphInput b)
    ‖WithLp.toLp 2 Ψ‖=1 ∧ ∃ β : ℝ, 1/32<β ∧ β≤1 ∧
      kernelProjector H y=β • u ∧ kernelProjector H (y-β • u)=0 := by
  have hα : 0<1+κ⁻¹ := by have := h.kappa_pos; positivity
  have hα2 : 1+κ⁻¹≤2 := by
    have hi : κ⁻¹≤1 := by
      rw [inv_eq_one_div]
      apply (div_le_iff₀ h.kappa_pos).mpr
      linarith [h.kappa_ge_two]
    linarith
  have hblock := exact_block_eq (physicalEncoding_exact κ h.kappa_pos s₀ UA A hA henc)
  have hInv : ‖Ring.inverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A)‖≤κ := by
    rw [← Perturbation.toEuclideanCLM_inverse A hunit]
    exact hinv
  have hp := graphInput_promises A hA
    (hunit.map (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)).toMonoidHom) h.kappa_pos
    (norm_le_of_exact_block henc) hInv b hb
  have hscale : ‖Ring.inverse (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) b‖=s := by
    rw [← Perturbation.toEuclideanCLM_inverse A hunit]
    simpa only [solutionScale,one_mul] using hs.symm
  dsimp only at hp
  rw [hscale] at hp
  dsimp only
  rw [originalPreparedState_eq s₀ i₀ h UA Ub b hcol]
  exact finite_preparation_coarse_component (physicalSignalZero s₀) h hα hα2
    (physicalEncoding κ h.kappa_pos UA) (physicalEncoding_hermitian κ h.kappa_pos UA)
    (graphMatrix A κ) (graphMatrix_hermitian A hA κ)
    (signalLift (S := Fin 4) Ub) (1,i₀) (graphInput b) hp.1
    (graphInput_source Ub i₀ b hcol) hblock hp.2.1 hp.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2

end OptimalQLS.Preparation
