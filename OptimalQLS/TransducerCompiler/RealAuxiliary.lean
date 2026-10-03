import OptimalQLS.TransducerCompiler.LoweredCircuit

noncomputable section
namespace OptimalQLS.TransducerCompiler
open Matrix BinaryClock

variable {n : Type*} [Fintype n] [DecidableEq n] {ℓ : ℕ}

private theorem inverse_real {a : Type*} [Fintype a] [DecidableEq a]
    (U : Matrix.unitaryGroup a ℂ) (hU : ∀ i j, (U.val i j).im = 0) (i j : a) :
    ((U⁻¹).val i j).im = 0 := by
  change ((star U.val) i j).im = 0
  simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, hU]

private theorem bitUnitary_real (U : Matrix.unitaryGroup (Space n (2^ℓ)) ℂ)
    (hU : ∀ i j, (U.val i j).im = 0) (i j : BitSpace n ℓ) :
    ((toBitUnitary U).val i j).im = 0 := hU _ _

private theorem cacheLift_real (U : Matrix.unitaryGroup (BitSpace n ℓ) ℂ)
    (hU : ∀ i j, (U.val i j).im = 0) (i j : CachedSpace n ℓ) :
    ((cacheLift U).val i j).im = 0 := by
  simp only [cacheLift, rewireUnitary, controlledOn, Matrix.submatrix_apply,
    Matrix.blockDiagonal_apply, ite_true]
  split_ifs
  · exact hU _ _
  · rfl

/-- The physical elementary instructions all have real coefficients, including their spectator wiring. -/
theorem elementary_real (g : GateSynthesis.LowerGate (LabelWire ℓ)) (i j : SynthSpace n ℓ) :
    ((lowerAuxHom g.eval).val i j).im = 0 :=
  GateSynthesis.placeHom_real _ _ (GateSynthesis.LowerGate.eval_real g) i j

/-- Both explicit tensor-Hadamard clock layers have real coefficients. -/
theorem synth_clock_real (adj : Bool) (S : Matrix.unitaryGroup (Base n) ℂ)
    (U₁ U₂ : Matrix.unitaryGroup n ℂ) (i j : SynthSpace n ℓ) :
    (((SynthInstruction.clock adj).eval S U₁ U₂).val i j).im = 0 := by
  apply GateSynthesis.placeHom_real
  apply cacheLift_real
  apply bitUnitary_real
  have hp : ∀ a b : Space n (2^ℓ),
      ((clockLift (n := n) (HadamardClock.finHadamard ℓ)).val a b).im = 0 :=
    clockLift_real _ (HadamardClock.finHadamard_real ℓ)
  cases adj with
  | false => exact hp
  | true => exact inverse_real _ hp

/-- Exactly the instructions excluded by the paper's “other than work and queries” clause. -/
def SynthInstruction.isAuxiliary : SynthInstruction ℓ → Bool
  | .elementary _ => true
  | .clock _ => true
  | _ => false

/-- Every auxiliary matrix in the complete compiler is real; this is independent of oracle values. -/
theorem auxiliary_real (g : SynthInstruction ℓ) (hg : g.isAuxiliary = true)
    (S : Matrix.unitaryGroup (Base n) ℂ) (U₁ U₂ : Matrix.unitaryGroup n ℂ)
    (i j : SynthSpace n ℓ) : ((g.eval S U₁ U₂).val i j).im = 0 := by
  cases g with
  | query₁ => simp [SynthInstruction.isAuxiliary] at hg
  | query₂ => simp [SynthInstruction.isAuxiliary] at hg
  | work => simp [SynthInstruction.isAuxiliary] at hg
  | elementary g => exact elementary_real g i j
  | clock adj => exact synth_clock_real adj S U₁ U₂ i j

end OptimalQLS.TransducerCompiler
