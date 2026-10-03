import OptimalQLS.TransducerCompiler.CachedTransport
import OptimalQLS.TransducerCompiler.Qubits

/-! # Error and cleanup of the gate-efficient cached compiler -/

noncomputable section
namespace OptimalQLS.TransducerCompiler
open Matrix BinaryClock

variable {n : Type*} [Fintype n] [DecidableEq n] {ℓ : ℕ}

def inputToBits (v : Space n (2^ℓ) → ℂ) : BitSpace n ℓ → ℂ := v ∘ spaceBitsEquiv

def cachedInput (b : Layout (2^ℓ)) (ξ : n → ℂ) : CachedSpace n ℓ → ℂ :=
  cleanVector (inputToBits (inputState b.zero ξ))

theorem toBit_mulVec (U : Matrix.unitaryGroup (Space n (2^ℓ)) ℂ)
    (v : Space n (2^ℓ) → ℂ) :
    (toBitUnitary U).val *ᵥ inputToBits v = inputToBits (U.val *ᵥ v) := by
  rw [toBitUnitary, rewire_apply]
  have hv : inputToBits v ∘ spaceBitsEquiv.symm = v := by
    ext z
    simp [inputToBits, Function.comp_def]
  rw [hv]
  rfl

theorem inputToBits_norm (v : Space n (2^ℓ) → ℂ) :
    ‖WithLp.toLp 2 (inputToBits v)‖ = ‖WithLp.toLp 2 v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, inputToBits, Function.comp_apply]
  exact (spaceBitsEquiv.sum_comp (fun z => ‖v z‖ ^ 2))

theorem cleanVector_sub (v w : BitSpace n ℓ → ℂ) :
    cleanVector (v-w) = cleanVector v - cleanVector w := by
  ext ⟨b,x,a⟩
  by_cases ha : a = (fun _ => false) <;> simp [cleanVector, ha]

/-- The efficient circuit has exactly the same error as the semantic finite compiler.
This equality also retains exact cleanup of the comparator register. -/
theorem cachedFinite_error_eq (b : Layout (2^ℓ)) (d₁ d₂ : ℕ)
    (h₁ : b.D₁ = 2^d₁) (h₂ : b.D₂ = 2^d₂)
    (S : Matrix.unitaryGroup (Base n) ℂ) (U₁ U₂ : Matrix.unitaryGroup n ℂ) (ξ τ : n → ℂ) :
    ‖WithLp.toLp 2 ((cachedFiniteUnitary ℓ d₁ d₂ S U₁ U₂).val *ᵥ cachedInput b ξ - cachedInput b τ)‖ =
      ‖Matrix.toEuclideanCLM (n := Space n (2^ℓ)) (𝕜 := ℂ)
          (hadamardFiniteUnitary b S U₁ U₂).val (WithLp.toLp 2 (inputState b.zero ξ)) -
        WithLp.toLp 2 (inputState b.zero τ)‖ := by
  simp only [cachedInput]
  rw [cachedFiniteUnitary_clean b d₁ d₂ h₁ h₂, toBit_mulVec, ← cleanVector_sub, cleanVector_norm]
  have hs : inputToBits ((hadamardFiniteUnitary b S U₁ U₂).val *ᵥ inputState b.zero ξ) -
      inputToBits (inputState b.zero τ) =
      inputToBits ((hadamardFiniteUnitary b S U₁ U₂).val *ᵥ inputState b.zero ξ - inputState b.zero τ) := rfl
  rw [hs, inputToBits_norm]
  rfl

/-- Actual finite clock/control-gate implementation, with the sharp weighted error bound. -/
theorem cachedFinite_error (b : Layout (2^ℓ)) (d₁ d₂ : ℕ)
    (h₁ : b.D₁ = 2^d₁) (h₂ : b.D₂ = 2^d₂)
    (S : Matrix.unitaryGroup (Base n) ℂ) (U₁ U₂ : Matrix.unitaryGroup n ℂ)
    (ξ τ v₀ v₁ v₂ : n → ℂ)
    (hS : S.val *ᵥ bundle ξ v₀ (U₁.val *ᵥ v₁) (U₂.val *ᵥ v₂) = bundle τ v₀ v₁ v₂) :
    ‖WithLp.toLp 2 ((cachedFiniteUnitary ℓ d₁ d₂ S U₁ U₂).val *ᵥ cachedInput b ξ - cachedInput b τ)‖ ≤
      2 / Real.sqrt ((2^ℓ : ℕ) : ℝ) *
        Real.sqrt (energy v₀ + b.D₁ * energy v₁ + b.D₂ * energy v₂) := by
  rw [cachedFinite_error_eq b d₁ d₂ h₁ h₂]
  exact hadamardFinite_error b S U₁ U₂ ξ τ v₀ v₁ v₂ hS

/-- A concrete bound on all real reversible primitives plus both Hadamard layers. -/
theorem cachedFinite_primitive_bound (ℓ d₁ d₂ : ℕ) :
    (cachedCompile ℓ d₁ d₂).primitiveGates +
      2 * (HadamardClock.circuit ℓ).gateCount ≤ 74 * 2^ℓ := by
  have hw : ℓ ≤ 2^ℓ := by
    induction ℓ with
    | zero => norm_num
    | succ ℓ ih =>
      rw [pow_succ]
      have hp : 0 < 2^ℓ := by positivity
      omega
  have h := cachedCompile_primitive_bound ℓ d₁ d₂
  rw [HadamardClock.circuit_gateCount]
  omega

end OptimalQLS.TransducerCompiler
