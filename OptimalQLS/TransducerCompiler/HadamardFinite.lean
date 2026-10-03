import OptimalQLS.TransducerCompiler.Finite
import OptimalQLS.TransducerCompiler.HadamardClock

noncomputable section
namespace OptimalQLS.TransducerCompiler
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {K : ℕ}

/-- Clock preparation semantics depend only on the actual zero column. -/
theorem prepare_input_of_column (P : Matrix.unitaryGroup (Fin K) ℂ) (zero : Fin K)
    (a : ℂ) (hP : P.val *ᵥ Pi.single zero 1 = fun _ => a) (ξ : n → ℂ) :
    (clockLift (n := n) P).val *ᵥ inputState zero ξ = a • publicState ξ := by
  ext ⟨⟨i,l⟩,k⟩
  rw [clockLift_apply]
  cases l with
  | pub =>
    have hcol : P.val k zero = a := by
      have h := congrFun hP k
      simpa only [Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply] using h
    have hv : (fun j => inputState zero ξ ((i,Label.pub),j)) = Pi.single zero (ξ i) := by
      ext j
      simp [inputState, Pi.single_apply]
    rw [hv, Matrix.mulVec_single]
    change P.val k zero * ξ i = _
    rw [hcol]
    simp [publicState]
  | internal => simp [inputState, publicState, Matrix.mulVec, dotProduct]
  | first => simp [inputState, publicState, Matrix.mulVec, dotProduct]
  | second => simp [inputState, publicState, Matrix.mulVec, dotProduct]

/-- The efficient dyadic-clock implementation uses tensor Hadamards, not the general reflection. -/
def hadamardFiniteUnitary {ℓ : ℕ} (b : Layout (2^ℓ)) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) : Matrix.unitaryGroup (Space n (2^ℓ)) ℂ :=
  (clockLift (HadamardClock.finHadamard ℓ))⁻¹ * (compile b).eval b S U₁ U₂ *
    clockLift (HadamardClock.finHadamard ℓ)

/-- The exact same catalyst/error bound holds for the genuine tensor-Hadamard clock circuit. -/
theorem hadamardFinite_error {ℓ : ℕ} (b : Layout (2^ℓ)) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) (ξ τ v₀ v₁ v₂ : n → ℂ)
    (hS : S.val *ᵥ bundle ξ v₀ (U₁.val *ᵥ v₁) (U₂.val *ᵥ v₂) = bundle τ v₀ v₁ v₂) :
    ‖Matrix.toEuclideanCLM (n := Space n (2^ℓ)) (𝕜 := ℂ) (hadamardFiniteUnitary b S U₁ U₂).val
        (WithLp.toLp 2 (inputState b.zero ξ)) - WithLp.toLp 2 (inputState b.zero τ)‖ ≤
      2 / Real.sqrt ((2^ℓ : ℕ) : ℝ) *
        Real.sqrt (energy v₀ + b.D₁ * energy v₁ + b.D₂ * energy v₂) := by
  rw [hadamardFiniteUnitary, conjugation_error]
  simp only [Matrix.toEuclideanCLM_toLp]
  have hz : b.zero = (⟨0, by positivity⟩ : Fin (2^ℓ)) := by apply Fin.ext; rfl
  have hp := HadamardClock.finHadamard_prepare ℓ
  rw [← hz] at hp
  rw [prepare_input_of_column _ b.zero _ hp ξ, prepare_input_of_column _ b.zero _ hp τ]
  exact compiled_uniform_error b S U₁ U₂ ξ τ v₀ v₁ v₂ hS

end OptimalQLS.TransducerCompiler
