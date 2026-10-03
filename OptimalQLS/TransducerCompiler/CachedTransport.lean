import OptimalQLS.TransducerCompiler.BitWiring
import OptimalQLS.TransducerCompiler.CachedCircuit
import OptimalQLS.TransducerCompiler.HadamardFinite

/-! # The efficient cached loop is the proved finite compiler, with clean ancillas -/

noncomputable section
namespace OptimalQLS.TransducerCompiler
open Matrix BinaryClock

variable {n : Type*} [Fintype n] [DecidableEq n] {ℓ : ℕ}

theorem idealBitOracleStage_eq (b : Layout (2^ℓ)) (d₁ d₂ : ℕ)
    (h₁ : b.D₁ = 2^d₁) (h₂ : b.D₂ = 2^d₂) (t : ℕ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) :
    idealBitOracleStage ℓ d₁ d₂ t U₁ U₂ = toBitUnitary (oracleStage b.D₁ b.D₂ t U₁ U₂) := by
  by_cases ht₁ : t % 2^d₁ = 0 <;> by_cases ht₂ : t % 2^d₂ = 0 <;>
    simp [idealBitOracleStage, oracleStage, h₁, h₂, ht₁, ht₂, toBit_mul, toBit_query, toBit_one]

theorem idealBitRound_eq (b : Layout (2^ℓ)) (d₁ d₂ : ℕ)
    (h₁ : b.D₁ = 2^d₁) (h₂ : b.D₂ = 2^d₂) (t : ℕ)
    (S : Matrix.unitaryGroup (Base n) ℂ) (U₁ U₂ : Matrix.unitaryGroup n ℂ) :
    idealBitRound ℓ d₁ d₂ t S U₁ U₂ = toBitUnitary (xorStep b S U₁ U₂ t) := by
  rw [xorStep, toBit_mul, toBit_mul, toBit_update b d₁ d₂ h₁ h₂,
    toBit_work, ← idealBitOracleStage_eq b d₁ d₂ h₁ h₂]
  rfl

theorem idealBitPrefix_eq (b : Layout (2^ℓ)) (d₁ d₂ : ℕ)
    (h₁ : b.D₁ = 2^d₁) (h₂ : b.D₂ = 2^d₂)
    (S : Matrix.unitaryGroup (Base n) ℂ) (U₁ U₂ : Matrix.unitaryGroup n ℂ) (t : ℕ) :
    idealBitPrefix ℓ d₁ d₂ S U₁ U₂ t = toBitUnitary (xorPrefix b S U₁ U₂ t) := by
  induction t with
  | zero => simp [idealBitPrefix, xorPrefix, toBit_one]
  | succ t ih =>
    rw [idealBitPrefix, idealBitRound_eq b d₁ d₂ h₁ h₂, ih, xorPrefix, toBit_mul]

/-- The full low-level cached body implements the original compiler exactly and cleans its cache. -/
theorem cachedCompile_eq_compiler (b : Layout (2^ℓ)) (d₁ d₂ : ℕ)
    (h₁ : b.D₁ = 2^d₁) (h₂ : b.D₂ = 2^d₂)
    (S : Matrix.unitaryGroup (Base n) ℂ) (U₁ U₂ : Matrix.unitaryGroup n ℂ)
    (v : BitSpace n ℓ → ℂ) :
    ((cachedCompile ℓ d₁ d₂).eval S U₁ U₂).val *ᵥ cleanVector v =
      cleanVector ((toBitUnitary ((compile b).eval b S U₁ U₂)).val *ᵥ v) := by
  rw [cachedCompile_cleanVector, idealBitPrefix_eq b d₁ d₂ h₁ h₂, xorPrefix_final]

/-- Pad an actual bit-space unitary by an untouched comparator register. -/
def cacheLift (U : Matrix.unitaryGroup (BitSpace n ℓ) ℂ) :
    Matrix.unitaryGroup (CachedSpace n ℓ) ℂ :=
  rewireUnitary (Equiv.prodAssoc (Base n) (Bits ℓ) (Bits ℓ))
    (controlledOn (fun _ : Bits ℓ => true) U)

/-- Padding with an unused cache preserves exact clean-cache semantics. -/
theorem cacheLift_cleanVector (U : Matrix.unitaryGroup (BitSpace n ℓ) ℂ)
    (v : BitSpace n ℓ → ℂ) :
    (cacheLift U).val *ᵥ cleanVector v = cleanVector (U.val *ᵥ v) := by
  ext ⟨b,x,a⟩
  rw [cacheLift, rewire_apply]
  simp only [Function.comp_apply, Equiv.prodAssoc_symm_apply]
  rw [controlledOn_apply]
  simp only [ite_true]
  by_cases ha : a = (fun _ => false)
  · simp [cleanVector, ha, Function.comp_def]
  · simp [cleanVector, ha, Function.comp_def, Matrix.mulVec, dotProduct]

/-- A fully specified efficient finite unitary, including real Hadamard clock gates. -/
def cachedFiniteUnitary (ℓ d₁ d₂ : ℕ) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) : Matrix.unitaryGroup (CachedSpace n ℓ) ℂ :=
  cacheLift (toBitUnitary ((clockLift (HadamardClock.finHadamard ℓ))⁻¹)) *
    (cachedCompile ℓ d₁ d₂).eval S U₁ U₂ *
      cacheLift (toBitUnitary (clockLift (HadamardClock.finHadamard ℓ)))

/-- No comparator leakage: the efficient circuit is exactly the semantic finite unitary
on every clean-cache input, with that cache returned to zero. -/
theorem cachedFiniteUnitary_clean (b : Layout (2^ℓ)) (d₁ d₂ : ℕ)
    (h₁ : b.D₁ = 2^d₁) (h₂ : b.D₂ = 2^d₂)
    (S : Matrix.unitaryGroup (Base n) ℂ) (U₁ U₂ : Matrix.unitaryGroup n ℂ)
    (v : BitSpace n ℓ → ℂ) :
    (cachedFiniteUnitary ℓ d₁ d₂ S U₁ U₂).val *ᵥ cleanVector v =
      cleanVector ((toBitUnitary (hadamardFiniteUnitary b S U₁ U₂)).val *ᵥ v) := by
  simp only [cachedFiniteUnitary, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
    cacheLift_cleanVector]
  rw [cachedCompile_eq_compiler b d₁ d₂ h₁ h₂, cacheLift_cleanVector]
  simp only [hadamardFiniteUnitary, toBit_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]

end OptimalQLS.TransducerCompiler
