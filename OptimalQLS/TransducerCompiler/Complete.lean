import OptimalQLS.TransducerCompiler.LoweredCounts
import OptimalQLS.TransducerCompiler.RealAuxiliary

/-! # Complete finite compiler with real elementary auxiliary gates -/

noncomputable section
namespace OptimalQLS.TransducerCompiler
open Matrix BinaryClock

variable {n : Type*} [Fintype n] [DecidableEq n] {ℓ : ℕ}

def synthInput (b : Layout (2^ℓ)) (ξ : n → ℂ) : SynthSpace n ℓ → ℂ :=
  synthClean (cachedInput b ξ)

theorem synthClean_norm (v : CachedSpace n ℓ → ℂ) :
    ‖WithLp.toLp 2 (synthClean v)‖ = ‖WithLp.toLp 2 v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, synthClean]

theorem synthClean_sub (v w : CachedSpace n ℓ → ℂ) :
    synthClean (v-w) = synthClean v - synthClean w := synthCleanMap.map_sub v w

/-- Lowering never changes the physical error, including all returned-zero ancillas. -/
theorem synthesize_error_eq (c : CachedCircuit ℓ) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) (v w : CachedSpace n ℓ → ℂ) :
    ‖WithLp.toLp 2 (((synthesize c).eval S U₁ U₂).val *ᵥ synthClean v - synthClean w)‖ =
      ‖WithLp.toLp 2 ((c.withClock S U₁ U₂).val *ᵥ v - w)‖ := by
  rw [synthesize_clean, ← synthClean_sub, synthClean_norm]

/-- The sharp BJY weighted-catalyst error for the literal real-gate compiler. -/
theorem complete_error (b : Layout (2^ℓ)) (d₁ d₂ : ℕ)
    (h₁ : b.D₁ = 2^d₁) (h₂ : b.D₂ = 2^d₂)
    (S : Matrix.unitaryGroup (Base n) ℂ) (U₁ U₂ : Matrix.unitaryGroup n ℂ)
    (ξ τ v₀ v₁ v₂ : n → ℂ)
    (hS : S.val *ᵥ bundle ξ v₀ (U₁.val *ᵥ v₁) (U₂.val *ᵥ v₂) = bundle τ v₀ v₁ v₂) :
    ‖WithLp.toLp 2 (((synthesize (cachedCompile ℓ d₁ d₂)).eval S U₁ U₂).val *ᵥ
      synthInput b ξ - synthInput b τ)‖ ≤
      2 / Real.sqrt ((2^ℓ : ℕ) : ℝ) *
        Real.sqrt (energy v₀ + b.D₁ * energy v₁ + b.D₂ * energy v₂) := by
  rw [synthInput, synthInput, synthesize_error_eq]
  exact cachedFinite_error b d₁ d₂ h₁ h₂ S U₁ U₂ ξ τ v₀ v₁ v₂ hS

/-- Exact cleanup of all comparator and synthesis ancillas on arbitrary coherent inputs.
The clock itself is retained in the ideal finite unitary, rather than incorrectly
asserted to be exactly zero on an approximate output. -/
theorem complete_cleanup (b : Layout (2^ℓ)) (d₁ d₂ : ℕ)
    (h₁ : b.D₁ = 2^d₁) (h₂ : b.D₂ = 2^d₂)
    (S : Matrix.unitaryGroup (Base n) ℂ) (U₁ U₂ : Matrix.unitaryGroup n ℂ)
    (v : BitSpace n ℓ → ℂ) :
    ((synthesize (cachedCompile ℓ d₁ d₂)).eval S U₁ U₂).val *ᵥ synthClean (cleanVector v) =
      synthClean (cleanVector ((toBitUnitary (hadamardFiniteUnitary b S U₁ U₂)).val *ᵥ v)) := by
  rw [synthesize_clean]
  change synthClean ((cachedFiniteUnitary ℓ d₁ d₂ S U₁ U₂).val *ᵥ cleanVector v) = _
  rw [cachedFiniteUnitary_clean b d₁ d₂ h₁ h₂]

/-- Exact black-box budgets after every auxiliary primitive has been lowered. -/
theorem complete_exact_counts (b : Layout (2^ℓ)) (d₁ d₂ : ℕ)
    (h₁ : b.D₁ = 2^d₁) (h₂ : b.D₂ = 2^d₂) :
    (synthesize (cachedCompile ℓ d₁ d₂)).workCalls = 2^ℓ ∧
    (synthesize (cachedCompile ℓ d₁ d₂)).firstCalls = 2^ℓ / b.D₁ ∧
    (synthesize (cachedCompile ℓ d₁ d₂)).secondCalls = 2^ℓ / b.D₂ := by
  have hs := synthesize_counts (cachedCompile ℓ d₁ d₂)
  have hc := cached_counts_eq_original b d₁ d₂ h₁ h₂
  have ho := compile_exact_counts b
  exact ⟨hs.1.trans (hc.1.trans ho.1), hs.2.1.trans (hc.2.1.trans ho.2.1),
    hs.2.2.1.trans (hc.2.2.trans ho.2.2)⟩

/-- A single complete circuit is chosen before every oracle, work matrix, and catalyst. -/
theorem finite_compiler_uniform (b : Layout (2^ℓ)) (d₁ d₂ : ℕ)
    (h₁ : b.D₁ = 2^d₁) (h₂ : b.D₂ = 2^d₂) :
    ∃ c : SynthCircuit ℓ,
      c.workCalls = 2^ℓ ∧ c.firstCalls = 2^ℓ / b.D₁ ∧ c.secondCalls = 2^ℓ / b.D₂ ∧
      c.auxGates ≤ 1110 * 2^ℓ ∧
      (∀ g : ℕ, c.chargedGates g ≤ (1110+g) * 2^ℓ) ∧
      ∀ (S : Matrix.unitaryGroup (Base n) ℂ) (U₁ U₂ : Matrix.unitaryGroup n ℂ)
        (ξ τ v₀ v₁ v₂ : n → ℂ),
        S.val *ᵥ bundle ξ v₀ (U₁.val *ᵥ v₁) (U₂.val *ᵥ v₂) = bundle τ v₀ v₁ v₂ →
        ‖WithLp.toLp 2 ((c.eval S U₁ U₂).val *ᵥ synthInput b ξ - synthInput b τ)‖ ≤
          2 / Real.sqrt ((2^ℓ : ℕ) : ℝ) *
            Real.sqrt (energy v₀ + b.D₁ * energy v₁ + b.D₂ * energy v₂) := by
  refine ⟨synthesize (cachedCompile ℓ d₁ d₂), ?_, ?_, ?_,
    synthesized_aux_bound ℓ d₁ d₂, synthesized_work_gate_bound ℓ d₁ d₂, ?_⟩
  · exact (complete_exact_counts b d₁ d₂ h₁ h₂).1
  · exact (complete_exact_counts b d₁ d₂ h₁ h₂).2.1
  · exact (complete_exact_counts b d₁ d₂ h₁ h₂).2.2
  · intro S U₁ U₂ ξ τ v₀ v₁ v₂ hS
    exact complete_error b d₁ d₂ h₁ h₂ S U₁ U₂ ξ τ v₀ v₁ v₂ hS

end OptimalQLS.TransducerCompiler
