import OptimalQLS.Preparation.CanonicalBounds
import OptimalQLS.TransducerCompiler.CompleteTheorems

/-! # Actual finite preparation from the canonical catalyst

This is the finite state/error/query assembly. Lowering its preparation work
and substituting original input oracles are separate subsequent layers.
-/
noncomputable section
namespace OptimalQLS.Preparation
open Matrix TransducerCompiler
variable {S D : Type*} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]

theorem preparation_mix_abs {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ) :
    |overlapMixingParameter κ ŝ|<1 :=
  abs_lt.mpr (overlapMixingParameter_mem h.kappa_pos h.estimate_pos)

def finitePreparationWork (s₀ : S) {κ s ŝ α : ℝ} (h : BudgetParameters κ s ŝ)
    (hα : 0<α) : Matrix.unitaryGroup (Base (Bool × (S × D))) ℂ :=
  compilerWork (signalProjector s₀) (signalProjector_star s₀) (signalProjector_idempotent s₀)
    (mul_pos hα h.estimate_pos) (preparation_mix_abs h)

/-- The exact fixed compiler word; this exposes the same witness to the
real-subspace alignment and physical gate-substitution proofs. -/
def preparationCompiler (κ ŝ : ℝ) : SynthCircuit (preparationExponent κ) :=
  synthesize (cachedCompile (preparationExponent κ) 0 (preparationPeriod κ ŝ))

/-- A single fully synthesized compiler word works for every promised actual
encoding and source unitary. All catalyst identities and energy bounds have
been proved from those matrices and their geometric promises. -/
theorem finite_preparation_error_uniform (s₀ : S) {κ s ŝ α : ℝ}
    (h : BudgetParameters κ s ŝ) (hα : 0<α) (hα2 : α≤2) :
    ∃ c : SynthCircuit (preparationExponent κ),
      c=preparationCompiler κ ŝ ∧ c.workCalls=mainBudget κ ∧ c.firstCalls=mainBudget κ ∧
      c.secondCalls=reflectionBudget κ ŝ ∧
      (c.firstCalls : ℝ)<256000000*κ ∧ (c.secondCalls : ℝ)<60000000*(κ/s) ∧
      c.auxGates≤1110*mainBudget κ ∧
      (∀ g : ℕ, c.chargedGates g≤(1110+g)*mainBudget κ) ∧
      ∀ (V : Matrix.unitaryGroup (S × D) ℂ)
        (hV : star (V : Matrix (S × D) (S × D) ℂ)=V)
        (H : Matrix D D ℂ) (hH : star H=H) (Ub : Matrix.unitaryGroup D ℂ)
        (i₀ : D) (e : EuclideanSpace ℂ D),
        ‖e‖=1 → (∀ i, Ub i i₀=e i) → H=α • signalBlock s₀ V →
        s^2/(2*κ^2) ≤
          ‖(LinearMap.ker (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H).toLinearMap).starProjection e‖^2 →
        ‖(LinearMap.ker (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H).toLinearMap).starProjection e‖^2≤s^2/κ^2 →
        ‖(LinearMap.ker (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) H).toLinearMap).starProjection e‖^2≤1/2 →
        ‖Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (matrixPseudoInverse H hH) e‖≤s →
        ‖WithLp.toLp 2
          (((c.eval (finitePreparationWork s₀ h hα) (doubleOracle V)
              (doubleOracle (signalLift (S := S) (preparedReflection Ub i₀)))).val*ᵥ
            synthInput h.layout (preparationInternal s₀ (WithLp.ofLp e))) -
            synthInput h.layout (preparationInternal s₀
              (preparationOutput H (preparedReflection Ub i₀) (overlapMixingParameter κ ŝ)
                (WithLp.ofLp e))))‖<(1:ℝ)/1000 := by
  let c := preparationCompiler κ ŝ
  have cnt := complete_exact_counts h.layout 0 (preparationPeriod κ ŝ)
    h.layout_D₁_dyadic h.layout_D₂_dyadic
  have ho := compile_exact_counts h.layout
  have hw : c.workCalls=mainBudget κ := cnt.1
  have hf : c.firstCalls=mainBudget κ :=
    cnt.2.1.trans (ho.2.1.symm.trans h.layout_exact_counts.2.1)
  have hs : c.secondCalls=reflectionBudget κ ŝ :=
    cnt.2.2.trans (ho.2.2.symm.trans h.layout_exact_counts.2.2)
  refine ⟨c,rfl,hw,hf,hs,?_,?_,synthesized_aux_bound _ _ _,synthesized_work_gate_bound _ _ _,?_⟩
  · rw [hf]; exact h.mainBudget_bounds.2
  · rw [hs]; exact h.reflectionBudget_scale_bound
  intro V hV H hH Ub i₀ e hen hcol hblock hp₁ hp₂ hp₃ hZ
  let r := overlapMixingParameter κ ŝ
  let q := preparationQ H (preparedReflection Ub i₀) r (WithLp.ofLp e)
  have hc := canonical_energy_bounds s₀ V hV H hH Ub i₀ e hen hcol
    h.kappa_ge_two h.scale_ge_one h.scale_le_kappa h.estimate_lower h.estimate_upper
    hα hα2 hblock hp₁ hp₂ hp₃ hZ
  apply h.finite_error_lt_of_energy (preparationInternal s₀ q)
    (preparationFirst s₀ V H hH α ŝ q) (preparationSecond s₀ H q) (norm_nonneg _)
    hc.2.1.le hc.2.2
  exact complete_error h.layout 0 (preparationPeriod κ ŝ) h.layout_D₁_dyadic h.layout_D₂_dyadic
    (finitePreparationWork s₀ h hα) (doubleOracle V)
    (doubleOracle (signalLift (S := S) (preparedReflection Ub i₀)))
    (preparationInternal s₀ (WithLp.ofLp e))
    (preparationInternal s₀ (preparationOutput H (preparedReflection Ub i₀) r (WithLp.ofLp e)))
    (preparationInternal s₀ q) (preparationFirst s₀ V H hH α ŝ q) (preparationSecond s₀ H q)
    (canonical_relation s₀ V hV H hH (preparedReflection Ub i₀) hα h.estimate_pos
      (preparation_mix_abs h) hblock (WithLp.ofLp e))

end OptimalQLS.Preparation
