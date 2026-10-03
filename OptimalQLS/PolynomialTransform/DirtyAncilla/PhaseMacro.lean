import OptimalQLS.PolynomialTransform.DirtyAncilla.LocalPhases

/-! # Coherent projected phases with three fixed scratch bits -/
noncomputable section
namespace OptimalQLS.PolynomialTransform.DirtyAncilla
open Matrix OptimalQLS.TransducerCompiler BinaryClock

def phaseMacro (n : ℕ) (φ : Bool → Circle) : List (PhaseGate (SmallWire n)) :=
  (elementaryZeroTest n).map PhaseGate.real ++ [.phase (smallTarget n) φ] ++
    (GateSynthesis.lowerProgram (zeroTest n).reverse).map PhaseGate.real

/-- At most 781(n+1) genuine one- or two-qubit gates. -/
theorem phaseMacro_length (n : ℕ) (φ : Bool → Circle) :
    (phaseMacro n φ).length ≤ 781*(n+1) := by
  have h := elementaryZeroTest_length n
  have h' := GateSynthesis.lowerProgram_length (zeroTest n).reverse
  have hz := zeroTest_length n
  simp only [List.length_reverse] at h'
  simp only [phaseMacro,List.length_append,List.length_map,List.length_cons,List.length_nil]
  omega

/-- The flag and synthesis bit start clean; the borrowed bit is arbitrary.
The exact basis-vector action restores all three bits and phases only on zero. -/
theorem phaseMacro_basis (n : ℕ) (φ : Bool → Circle) (b : SmallWire n → Bool)
    (hb : b (smallTarget n)=false) :
    (phaseEval (phaseMacro n φ)).val *ᵥ Pi.single (false,b) (1 : ℂ)=
      (φ (decide (∀ i : Fin n, b (.inl i)=false)) : ℂ) • (Pi.single (false,b) 1 : GateSynthesis.Space (SmallWire n) → ℂ) := by
  simp only [phaseMacro,phaseEval_append,phaseEval_real,phaseEval,List.map_nil,
    PhaseGate.eval,one_mul,Submonoid.coe_mul,← Matrix.mulVec_mulVec]
  rw [elementaryZeroTest,GateSynthesis.lowerProgram_basis,localPhase_eq,diagonalPhase_basis,
    Matrix.mulVec_smul,GateSynthesis.lowerProgram_basis,run_reverse_run]
  congr 2
  simp [zeroTest_run,hb]

def cleanBits {n : ℕ} (x : Fin n → Bool) (dirty : Bool) : SmallWire n → Bool
  | .inl i => x i
  | .inr i => if i=0 then false else dirty

theorem cleanBits_target {n : ℕ} (x : Fin n → Bool) (dirty : Bool) :
    cleanBits x dirty (smallTarget n)=false := by simp [cleanBits,smallTarget]

/-- Coherent zero phase acts on every input signal string, with no dependence
on the initial borrowed bit. -/
theorem phaseMacro_clean_basis (n : ℕ) (φ : Bool → Circle) (x : Fin n → Bool) (dirty : Bool) :
    (phaseEval (phaseMacro n φ)).val *ᵥ Pi.single (false,cleanBits x dirty) (1 : ℂ)=
      (φ (decide (x=fun _ => false)) : ℂ) • (Pi.single (false,cleanBits x dirty) 1 : GateSynthesis.Space (SmallWire n) → ℂ) := by
  have h := phaseMacro_basis n φ (cleanBits x dirty) (cleanBits_target x dirty)
  have he : (∀ i : Fin n, cleanBits x dirty (.inl i)=false) ↔ x=(fun _ => false) := by
    simp only [cleanBits]; exact funext_iff.symm
  simpa only [he] using h

/-- Explicit clean embedding of an arbitrary signal superposition. -/
def phaseCleanVector {n : ℕ} (dirty : Bool) (v : (Fin n → Bool) → ℂ) :
    GateSynthesis.Space (SmallWire n) → ℂ :=
  ∑ x, v x • (Pi.single (false,cleanBits x dirty) 1 : GateSynthesis.Space (SmallWire n) → ℂ)

/-- Linear extension supplies the coherent, rather than basis-only, theorem. -/
theorem phaseMacro_cleanVector (n : ℕ) (φ : Bool → Circle) (dirty : Bool)
    (v : (Fin n → Bool) → ℂ) :
    (phaseEval (phaseMacro n φ)).val *ᵥ phaseCleanVector dirty v =
      phaseCleanVector dirty (fun x => (φ (decide (x=fun _ => false)) : ℂ) * v x) := by
  simp only [phaseCleanVector,Matrix.mulVec_sum,Matrix.mulVec_smul,phaseMacro_clean_basis]
  apply Finset.sum_congr rfl
  intro x _
  rw [smul_smul,mul_comm]

end OptimalQLS.PolynomialTransform.DirtyAncilla
