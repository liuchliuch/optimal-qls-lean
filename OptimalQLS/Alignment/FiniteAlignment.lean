import OptimalQLS.Alignment.PreparationInvariant
import OptimalQLS.TransducerCompiler.Complete
import OptimalQLS.Preparation.Finite

/-! # Lemma 4.9 for the actual synthesized finite preparation circuit

The state below is obtained from the explicit instruction list. The public
zero-auxiliary slice belongs to the real Krylov space, and its kernel projection
is exactly a real multiple of the normalized projected input. -/
noncomputable section
namespace OptimalQLS.Alignment
open Matrix Preparation TransducerCompiler
variable {S D : Type*} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]

/-- Bra-zero on the label, spare data bit, signal, clock, cache, and synthesis
ancilla, leaving precisely the original data register. -/
def zeroAuxiliaryOutput {ℓ : ℕ} (s₀ : S)
    (Ψ : SynthSpace (Bool × (S × D)) ℓ → ℂ) : D → ℂ :=
  fun i => Ψ (false,(((false,(s₀,i)),.pub),(fun _ => false),(fun _ => false)))

/-- Literal fully synthesized finite preparation, with no invariant or
restoration certificate among its arguments. -/
def actualPreparationState {ℓ : ℕ} (s₀ : S) (b : Layout (2^ℓ)) (d₁ d₂ : ℕ)
    {μ r : ℝ} (hμ : 0<μ) (hr : |r|<1)
    (V : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup D ℂ)
    (i₀ : D) (e : D → ℂ) : SynthSpace (Bool × (S × D)) ℓ → ℂ :=
  ((synthesize (cachedCompile ℓ d₁ d₂)).eval
    (compilerWork (signalProjector s₀) (signalProjector_star s₀)
      (signalProjector_idempotent s₀) hμ hr)
    (doubleOracle V) (doubleOracle (signalLift (S := S) (preparedReflection Ub i₀)))).val*ᵥ
      synthInput b (doubleVector (signalInjection s₀*ᵥe) 0)

/-- The only matrix premises are the actual Hermitian block encoding and
prepared-vector promises. The real invariant is proved from the gate sequence. -/
theorem actualPreparation_zero_mem {ℓ : ℕ} (s₀ : S) (b : Layout (2^ℓ)) (d₁ d₂ : ℕ)
    (h₁ : b.D₁=2^d₁) (h₂ : b.D₂=2^d₂)
    {α μ r : ℝ} (hα : α≠0) (hμ : 0<μ) (hr : |r|<1)
    (V : Matrix.unitaryGroup (S × D) ℂ) (hV : star V.val=V.val)
    (H : Matrix D D ℂ) (hH : star H=H) (Ub : Matrix.unitaryGroup D ℂ)
    (i₀ : D) (e : EuclideanSpace ℂ D) (he : ‖e‖=1) (hcol : ∀ i,Ub i i₀=e i)
    (hblock : H=α • signalBlock s₀ V) :
    zeroAuxiliaryOutput s₀ (actualPreparationState s₀ b d₁ d₂ hμ hr V Ub i₀ (WithLp.ofLp e)) ∈
      dataKrylov H (WithLp.ofLp e) := by
  let N := signalKrylov s₀ H (WithLp.ofLp e)
  let M := oracleSpan N V.val
  let P := preparationSectors N M
  have hout := synthesized_zero_slice_mem P b d₁ d₂ h₁ h₂
    (compilerWork (signalProjector s₀) (signalProjector_star s₀)
      (signalProjector_idempotent s₀) hμ hr)
    (doubleOracle V) (doubleOracle (signalLift (S := S) (preparedReflection Ub i₀)))
    (fun v hv => encodedCompilerWork_preserves s₀ H (WithLp.ofLp e) V hα hblock hμ hr hv)
    (fun x hx => encodedFirst_preserves s₀ H (WithLp.ofLp e) V hV hx)
    (fun x hx => encodedSecond_preserves s₀ H hH e he Ub i₀ hcol M hx)
    (encodedInput_mem s₀ H (WithLp.ofLp e) M) Label.pub
  exact signalKrylov_slice s₀ H (WithLp.ofLp e) hout.1

/-- Lemma 4.9: the coefficient is real for the actual fully lowered finite
preparation circuit. No approximate projection is used in this statement. -/
theorem lemma49_exact_alignment {ℓ : ℕ} (s₀ : S) (b : Layout (2^ℓ)) (d₁ d₂ : ℕ)
    (h₁ : b.D₁=2^d₁) (h₂ : b.D₂=2^d₂)
    {α μ r : ℝ} (hα : α≠0) (hμ : 0<μ) (hr : |r|<1)
    (V : Matrix.unitaryGroup (S × D) ℂ) (hV : star V.val=V.val)
    (H : Matrix D D ℂ) (hH : star H=H) (Ub : Matrix.unitaryGroup D ℂ)
    (i₀ : D) (e : EuclideanSpace ℂ D) (he : ‖e‖=1) (hcol : ∀ i,Ub i i₀=e i)
    (hblock : H=α • signalBlock s₀ V) :
    ∃ β : ℝ,
      kernelProjector H (WithLp.toLp 2 (zeroAuxiliaryOutput s₀
        (actualPreparationState s₀ b d₁ d₂ hμ hr V Ub i₀ (WithLp.ofLp e)))) =
      β • normalizedProjectedInput H e :=
  dataKrylov_exact_alignment H hH e
    (actualPreparation_zero_mem s₀ b d₁ d₂ h₁ h₂ hα hμ hr V hV H hH Ub i₀ e he hcol hblock)

/-- The very same selected circuit used by the finite-accuracy theorem. -/
def finitePreparedState (s₀ : S) {κ s ŝ α : ℝ} (h : BudgetParameters κ s ŝ) (hα : 0<α)
    (V : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup D ℂ)
    (i₀ : D) (e : D → ℂ) : SynthSpace (Bool × (S × D)) (preparationExponent κ) → ℂ :=
  ((preparationCompiler κ ŝ).eval (finitePreparationWork s₀ h hα) (doubleOracle V)
    (doubleOracle (signalLift (S := S) (preparedReflection Ub i₀)))).val*ᵥ
      synthInput h.layout (preparationInternal s₀ e)

theorem finitePreparedState_zero_mem (s₀ : S) {κ s ŝ α : ℝ}
    (h : BudgetParameters κ s ŝ) (hα : 0<α)
    (V : Matrix.unitaryGroup (S × D) ℂ) (hV : star V.val=V.val)
    (H : Matrix D D ℂ) (hH : star H=H) (Ub : Matrix.unitaryGroup D ℂ)
    (i₀ : D) (e : EuclideanSpace ℂ D) (he : ‖e‖=1) (hcol : ∀ i,Ub i i₀=e i)
    (hblock : H=α • signalBlock s₀ V) :
    zeroAuxiliaryOutput s₀ (finitePreparedState s₀ h hα V Ub i₀ (WithLp.ofLp e)) ∈
      dataKrylov H (WithLp.ofLp e) :=
  actualPreparation_zero_mem s₀ h.layout 0 (preparationPeriod κ ŝ)
    h.layout_D₁_dyadic h.layout_D₂_dyadic hα.ne' (mul_pos hα h.estimate_pos)
    (preparation_mix_abs h) V hV H hH Ub i₀ e he hcol hblock

/-- Lemma 4.9 for the chosen preparationCompiler, not an existential compiler
with an assumed final invariant. -/
theorem lemma49_preparationCompiler (s₀ : S) {κ s ŝ α : ℝ}
    (h : BudgetParameters κ s ŝ) (hα : 0<α)
    (V : Matrix.unitaryGroup (S × D) ℂ) (hV : star V.val=V.val)
    (H : Matrix D D ℂ) (hH : star H=H) (Ub : Matrix.unitaryGroup D ℂ)
    (i₀ : D) (e : EuclideanSpace ℂ D) (he : ‖e‖=1) (hcol : ∀ i,Ub i i₀=e i)
    (hblock : H=α • signalBlock s₀ V) :
    ∃ β : ℝ, kernelProjector H (WithLp.toLp 2 (zeroAuxiliaryOutput s₀
      (finitePreparedState s₀ h hα V Ub i₀ (WithLp.ofLp e)))) =
      β • normalizedProjectedInput H e :=
  dataKrylov_exact_alignment H hH e
    (finitePreparedState_zero_mem s₀ h hα V hV H hH Ub i₀ e he hcol hblock)

end OptimalQLS.Alignment
