import OptimalQLS.GraphEncoding.SingleFlagOracle
import OptimalQLS.GraphEncoding.ControlledRealGates
import OptimalQLS.PolynomialTransform.CleanEmbedding

/-! # Literal mixed-polarity phase tests for preparation

The flag is computed by an actual reversible program and uncomputed after a
one-qubit phase. The synthesis and flag bits return clean; the third scratch
bit can be borrowed in an arbitrary computational value.
-/
noncomputable section
set_option maxHeartbeats 1000000
namespace OptimalQLS.Preparation.CompilerAttachment
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla GraphEncoding
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A genuine compute/one-bit phase/uncompute list, including polarity changes. -/
def maskedPhaseCode (m : ℕ) (f : SmallWire m → ι) (hf : Function.Injective f)
    (mask : Fin m → Bool) (φ : Bool → Circle) : List (PhaseGate ι) :=
  (TransducerCompiler.GateSynthesis.lowerProgram (maskComputeProgram m f hf mask)).map PhaseGate.real ++
    [.phase (f (smallTarget m)) φ] ++
    (TransducerCompiler.GateSynthesis.lowerProgram (maskComputeProgram m f hf mask).reverse).map PhaseGate.real

theorem maskedPhaseCode_length (m : ℕ) (f : SmallWire m → ι) (hf : Function.Injective f)
    (mask : Fin m → Bool) (φ : Bool → Circle) :
    (maskedPhaseCode m f hf mask φ).length ≤ 30*(m+26*(m+1))+1 := by
  have hl := TransducerCompiler.GateSynthesis.lowerProgram_length (maskComputeProgram m f hf mask)
  have hr := TransducerCompiler.GateSynthesis.lowerProgram_length (maskComputeProgram m f hf mask).reverse
  have hp := maskComputeProgram_length m f hf mask
  simp only [List.length_reverse] at hr
  simp only [maskedPhaseCode,List.length_append,List.length_map,List.length_cons,List.length_nil]
  omega

theorem maskedPhaseCode_basis (m : ℕ) (f : SmallWire m → ι) (hf : Function.Injective f)
    (mask : Fin m → Bool) (φ : Bool → Circle) (b : ι → Bool)
    (hb : b (f (smallTarget m))=false) :
    (phaseEval (maskedPhaseCode m f hf mask φ)).val *ᵥ Pi.single (false,b) 1 =
      (φ (decide (∀ k : Fin m, b (f (.inl k))=mask k)) : ℂ) •
        (Pi.single (false,b) 1 : TransducerCompiler.GateSynthesis.Space ι → ℂ) := by
  simp only [maskedPhaseCode,phaseEval_append,phaseEval_real,phaseEval,
    PhaseGate.eval,one_mul,Submonoid.coe_mul,← Matrix.mulVec_mulVec]
  rw [TransducerCompiler.GateSynthesis.lowerProgram_basis,localPhase_eq,diagonalPhase_basis,
    Matrix.mulVec_smul,TransducerCompiler.GateSynthesis.lowerProgram_basis,run_reverse_run]
  simp only [Prod.snd,maskComputeProgram_flag m f hf mask b hb]

/-- The phase is negative precisely when all supplied literals match. -/
def matchSign (b : Bool) : Circle := if b then ⟨-1, by simp [Submonoid.unitSphere,Metric.mem_sphere,dist_zero_right]⟩ else 1

@[simp] theorem matchSign_val (b : Bool) : (matchSign b : ℂ)=if b then -1 else 1 := by
  cases b <;> rfl

theorem maskedPhaseCode_real (m : ℕ) (f : SmallWire m → ι) (hf : Function.Injective f)
    (mask : Fin m → Bool) :
    ∀ g ∈ maskedPhaseCode m f hf mask matchSign, RealPhaseGate g := by
  intro g hg
  simp only [maskedPhaseCode,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with (hg|hg)|hg
  · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hg
    exact realPhaseGate_real r
  · subst g
    intro i j
    change ((localPhase (f (smallTarget m)) matchSign).val i j).im=0
    rw [localPhase_eq]
    simp only [diagonalPhase,Matrix.diagonal_apply]
    split_ifs <;> simp [matchSign_val]
    split_ifs <;> simp
  · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hg
    exact realPhaseGate_real r

end OptimalQLS.Preparation.CompilerAttachment
