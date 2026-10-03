import OptimalQLS.Preparation.Energy
import OptimalQLS.Preparation.MatrixGuarantees
import OptimalQLS.Preparation.PlaneCosts

noncomputable section
namespace OptimalQLS.Preparation
open Matrix TransducerCompiler
variable {S D : Type*} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]

/-- Explicit canonical preparation vectors. These are algebraic definitions,
not witnesses for a separately assumed transduction certificate. -/
def preparationQ (H : Matrix D D ℂ) (R : Matrix.unitaryGroup D ℂ) (r : ℝ) (ξ : D → ℂ) : D → ℂ :=
  fractionalCatalyst (idealUnitary H R) r ξ

def preparationOutput (H : Matrix D D ℂ) (R : Matrix.unitaryGroup D ℂ) (r : ℝ) (ξ : D → ℂ) : D → ℂ :=
  fractionalAction (idealUnitary H R) r*ᵥξ

def preparationInternal (s₀ : S) (q : D → ℂ) : Bool × (S × D) → ℂ :=
  doubleVector (signalInjection s₀*ᵥq) 0

def preparationFirst (s₀ : S) (V : Matrix.unitaryGroup (S × D) ℂ)
    (H : Matrix D D ℂ) (hH : star H=H) (α τ : ℝ) (q : D → ℂ) : Bool × (S × D) → ℂ :=
  let p := signalInjection s₀*ᵥ(matrixKernelProjection H*ᵥq)
  let z := signalInjection s₀*ᵥ(matrixPseudoInverse H hH*ᵥq)
  doubleVector (kernelCatalystOne V (α*τ) α p z) (kernelCatalystTwo V (α*τ) α p z)

def preparationSecond (s₀ : S) (H : Matrix D D ℂ) (q : D → ℂ) : Bool × (S × D) → ℂ :=
  doubleVector ((2:ℝ) • (signalInjection s₀*ᵥ(matrixKernelProjection H*ᵥq))-signalInjection s₀*ᵥq) 0

/-- Canonical four-sector identity from the actual exact Hermitian encoding. -/
theorem canonical_relation (s₀ : S)
    (V : Matrix.unitaryGroup (S × D) ℂ) (hV : star (V : Matrix (S × D) (S × D) ℂ)=V)
    (H : Matrix D D ℂ) (hH : star H=H) (R : Matrix.unitaryGroup D ℂ)
    {α τ r : ℝ} (hα : 0<α) (hτ : 0<τ) (hr : |r|<1)
    (hblock : H=α • signalBlock s₀ V) (ξ : D → ℂ) :
    let q := preparationQ H R r ξ
    let Swork := compilerWork (signalProjector (D := D) s₀)
      (signalProjector_star s₀) (signalProjector_idempotent s₀) (mul_pos hα hτ) hr
    Swork.val*ᵥbundle (preparationInternal s₀ ξ) (preparationInternal s₀ q)
      ((doubleOracle V).val*ᵥpreparationFirst s₀ V H hH α τ q)
      ((doubleOracle (signalLift (S := S) R)).val*ᵥpreparationSecond s₀ H q) =
      bundle (preparationInternal s₀ (preparationOutput H R r ξ)) (preparationInternal s₀ q)
        (preparationFirst s₀ V H hH α τ q) (preparationSecond s₀ H q) := by
  dsimp only [preparationQ,preparationOutput,preparationInternal,preparationFirst,preparationSecond]
  apply compilerRelation_of_circuit
  exact encodedPreparation_transduction s₀ V hV H hH R hα hτ hr hblock ξ

@[simp] theorem preparationInternal_energy (s₀ : S) (q : D → ℂ) :
    energy (preparationInternal s₀ q)=energy q := by
  rw [preparationInternal,doubleVector_energy,zero_energy,add_zero,signal_energy]

@[simp] theorem preparationSecond_energy (s₀ : S) (H : Matrix D D ℂ) (q : D → ℂ) :
    energy (preparationSecond s₀ H q)=energy q := by
  rw [preparationSecond,doubleVector_energy,zero_energy,add_zero,
    ← Matrix.mulVec_smul,← Matrix.mulVec_sub,signal_energy,kernel_reflection_energy]

theorem preparationFirst_energy (s₀ : S)
    (V : Matrix.unitaryGroup (S × D) ℂ) (hV : star (V : Matrix (S × D) (S × D) ℂ)=V)
    (H : Matrix D D ℂ) (hH : star H=H) {α τ : ℝ} (hα : 0<α) (hτ : 0<τ)
    (hblock : H=α • signalBlock s₀ V) (q : D → ℂ) :
    energy (preparationFirst s₀ V H hH α τ q) =
      2*α*(τ*‖(LinearMap.ker (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H).toLinearMap).starProjection
        (WithLp.toLp 2 q)‖^2+
        ‖Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (matrixPseudoInverse H hH) (WithLp.toLp 2 q)‖^2/τ) := by
  obtain ⟨h₁,h₂⟩ := kernelReflection_catalyst_norms s₀ V hV H hH hα hτ hblock (WithLp.toLp 2 q)
  dsimp only at h₁ h₂
  rw [preparationFirst,doubleVector_energy,energy_eq_norm_sq,energy_eq_norm_sq,h₁,h₂]
  simp only [matrixKernelProjection,StarAlgEquiv.apply_symm_apply]
  ring

end OptimalQLS.Preparation
