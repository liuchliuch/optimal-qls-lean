import OptimalQLS.PolynomialTransform.DirtyAncilla.PhaseMacro

/-! # Controlled projected phase with shared constant scratch -/
noncomputable section
namespace OptimalQLS.PolynomialTransform.DirtyAncilla
open Matrix OptimalQLS.TransducerCompiler BinaryClock
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mappedZeroTest (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f) : Program ι :=
  mapProgram f hf (zeroTest n)

theorem mappedZeroTest_run (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (b : ι → Bool) :
    run (mappedZeroTest n f hf) b=Function.update b (f (smallTarget n))
      (Bool.xor (b (f (smallTarget n))) (decide (∀ i : Fin n, b (f (.inl i))=false))) := by
  simpa only [Function.comp_def,mappedZeroTest] using mapProgram_target f hf (zeroTest n)
    (smallTarget n) (fun b => Bool.xor (b (smallTarget n))
      (decide (∀ i : Fin n, b (.inl i)=false))) (zeroTest_run n) b

/-- A two-qubit phase reads an ordinary control and the coherently computed zero flag. -/
def controlledPhaseMacro (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (c : ι) (hc : c ≠ f (smallTarget n)) (φ : Bool × Bool → Circle) : List (PhaseGate ι) :=
  (GateSynthesis.lowerProgram (mappedZeroTest n f hf)).map PhaseGate.real ++
    [.pairPhase c (f (smallTarget n)) hc φ] ++
    (GateSynthesis.lowerProgram (mappedZeroTest n f hf).reverse).map PhaseGate.real

theorem controlledPhaseMacro_length (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (c : ι) (hc : c ≠ f (smallTarget n)) (φ : Bool × Bool → Circle) :
    (controlledPhaseMacro n f hf c hc φ).length ≤ 781*(n+1) := by
  have h := GateSynthesis.lowerProgram_length (mappedZeroTest n f hf)
  have h' := GateSynthesis.lowerProgram_length (mappedZeroTest n f hf).reverse
  have hz := zeroTest_length n
  simp only [List.length_reverse,mappedZeroTest,mapProgram_length] at h h'
  simp only [controlledPhaseMacro,mappedZeroTest,List.length_append,List.length_map,List.length_cons,List.length_nil]
  omega

/-- Exact coherent action with both clean bits restored; every borrowed and
spectator bit returns unchanged, including the ordinary control. -/
theorem controlledPhaseMacro_basis (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (c : ι) (hc : c ≠ f (smallTarget n)) (φ : Bool × Bool → Circle) (b : ι → Bool)
    (hb : b (f (smallTarget n))=false) :
    (phaseEval (controlledPhaseMacro n f hf c hc φ)).val *ᵥ Pi.single (false,b) (1 : ℂ)=
      (φ (b c,decide (∀ i : Fin n, b (f (.inl i))=false)) : ℂ) •
        (Pi.single (false,b) 1 : GateSynthesis.Space ι → ℂ) := by
  simp only [controlledPhaseMacro,phaseEval_append,phaseEval_real,phaseEval,List.map_nil,
    PhaseGate.eval,one_mul,Submonoid.coe_mul,← Matrix.mulVec_mulVec]
  rw [GateSynthesis.lowerProgram_basis,localPairPhase_eq,diagonalPhase_basis,
    Matrix.mulVec_smul,GateSynthesis.lowerProgram_basis,run_reverse_run]
  congr 2
  simp [mappedZeroTest_run,hb,hc]

end OptimalQLS.PolynomialTransform.DirtyAncilla
