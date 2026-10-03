import OptimalQLS.GraphEncoding.ControlledRealGates
import OptimalQLS.PolynomialTransform.ElementaryCircuit

/-! # Literal predicate computation around a singly controlled original oracle -/
noncomputable section
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
namespace OptimalQLS.GraphEncoding
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
variable {ι A B : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- This port reads exactly one named flag qubit. No Boolean predicate is free. -/
def singleFlagOraclePort (A : Type*) (t : ι) : QueryPort A (TransducerCompiler.GateSynthesis.Space ι × A) where
  multiplicity := Fintype.card (TransducerCompiler.GateSynthesis.Space ι)
  wiring := (Equiv.prodCongr (Equiv.refl A)
    (Fintype.equivFin (TransducerCompiler.GateSynthesis.Space ι)).symm).trans
      (Equiv.prodComm A (TransducerCompiler.GateSynthesis.Space ι))
  control := fun k => ((Fintype.equivFin (TransducerCompiler.GateSynthesis.Space ι)).symm k).2 t

theorem singleFlagOracle_entries (t : ι) (U : Matrix.unitaryGroup A ℂ)
    (z r : Bool) (b c : ι → Bool) (i j : A) :
    ((singleFlagOraclePort A t).apply U).val ((z,b),i) ((r,c),j) =
      if (z,b)=(r,c) then (if b t then U.val i j else if i=j then 1 else 0) else 0 := by
  simp [singleFlagOraclePort,QueryPort.apply,rewireUnitary,controlledUnitary,
    Matrix.blockDiagonal_apply,Matrix.one_apply]
  split_ifs <;> simp_all [Matrix.one_apply]

theorem singleFlagOracle_basis (t : ι) (U : Matrix.unitaryGroup A ℂ)
    (z : Bool) (b : ι → Bool) (i : A) :
    ((singleFlagOraclePort A t).apply U).val *ᵥ Pi.single ((z,b),i) 1 =
      ∑ j : A, (if b t then U.val j i else if j=i then 1 else 0) •
        (Pi.single ((z,b),j) 1 : TransducerCompiler.GateSynthesis.Space ι × A → ℂ) := by
  ext ⟨⟨r,c⟩,j⟩
  simp only [Matrix.mulVec_single_one,Matrix.col_apply,singleFlagOracle_entries,
    Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
  by_cases h : (r,c)=(z,b)
  · rcases Prod.mk.inj h with ⟨rfl,rfl⟩
    simp
  · simp [h, Prod.mk.injEq]

/-- The reversible code computes the literal masked conjunction into a clean flag. -/
def maskComputeProgram (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (mask : Fin n → Bool) : Program ι :=
  maskFlipProgram n f mask ++ mappedZeroTest n f hf

theorem maskComputeProgram_flag (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (mask : Fin n → Bool) (b : ι → Bool) (hb : b (f (smallTarget n))=false) :
    run (maskComputeProgram n f hf mask) b (f (smallTarget n)) =
      decide (∀ i : Fin n, b (f (.inl i))=mask i) := by
  have hf0 : run (maskFlipProgram n f mask) b (f (smallTarget n)) = false := by
    rw [maskFlipProgram_other n f hf]
    · exact hb
    · intro i hi
      have hh := hf hi
      cases hh
  have hp : (∀ i : Fin n, run (maskFlipProgram n f mask) b (f (.inl i))=false) ↔
      ∀ i : Fin n, b (f (.inl i))=mask i := by
    simp only [maskFlipProgram_control n f hf]
    apply forall_congr'
    intro i
    cases b (f (.inl i)) <;> cases mask i <;> simp
  simp [maskComputeProgram,run_append,mappedZeroTest_run,hf0,hp]

def realProgramCircuit (A B : Type*) [Fintype A] [DecidableEq A] (p : Program ι) : ElementaryCircuit A B ι A :=
  elementaryMacro ((TransducerCompiler.GateSynthesis.lowerProgram p).map PhaseGate.real)

theorem realProgramCircuit_basis (p : Program ι) (b : ι → Bool) (i : A)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    ((realProgramCircuit A B p).toQuery.eval UA Ub).val *ᵥ Pi.single ((false,b),i) 1 =
      Pi.single ((false,run p b),i) 1 := by
  rw [realProgramCircuit,elementaryMacro_eval,phaseEval_real]
  exact TransducerCompiler.GateSynthesis.placeHom_basis (Equiv.refl _)
    (TransducerCompiler.GateSynthesis.eval (TransducerCompiler.GateSynthesis.lowerProgram p))
    (false,b) (false,run p b) i (TransducerCompiler.GateSynthesis.lowerProgram_basis p b)

/-- Compute, one actual single-flag-controlled query (possibly adjoint), uncompute. -/
def maskedOracleCircuit (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (mask : Fin n → Bool) (adj : Bool) : ElementaryCircuit A B ι A :=
  realProgramCircuit A B (maskComputeProgram n f hf mask) ++
  [.matrixCall (singleFlagOraclePort A (f (smallTarget n))) adj] ++
  realProgramCircuit A B (maskComputeProgram n f hf mask).reverse

theorem maskedOracleCircuit_basis (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (mask : Fin n → Bool) (adj : Bool) (b : ι → Bool) (hb : b (f (smallTarget n))=false)
    (i : A) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    ((maskedOracleCircuit n f hf mask adj).toQuery.eval UA Ub).val *ᵥ Pi.single ((false,b),i) 1 =
      ∑ j : A, (if decide (∀ k : Fin n, b (f (.inl k))=mask k)
        then (if adj then UA⁻¹ else UA).val j i else if j=i then 1 else 0) •
          (Pi.single ((false,b),j) 1 : TransducerCompiler.GateSynthesis.Space ι × A → ℂ) := by
  simp only [maskedOracleCircuit,ElementaryCircuit.toQuery_append,QueryCircuit.eval_append,
    Submonoid.coe_mul,← Matrix.mulVec_mulVec]
  rw [realProgramCircuit_basis]
  have hs : QueryCircuit.eval UA Ub (ElementaryCircuit.toQuery
      ([ElementaryInstruction.matrixCall (singleFlagOraclePort A (f (smallTarget n))) adj] :
        ElementaryCircuit A B ι A)) =
      (singleFlagOraclePort A (f (smallTarget n))).apply (if adj then UA⁻¹ else UA) := by
    simp [ElementaryCircuit.toQuery,ElementaryInstruction.toQuery,QueryCircuit.eval,QueryInstruction.eval]
  rw [hs]
  rw [singleFlagOracle_basis,Matrix.mulVec_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mulVec_smul,realProgramCircuit_basis,run_reverse_run,
    maskComputeProgram_flag n f hf mask b hb]

theorem maskComputeProgram_length (n : ℕ) (f : SmallWire n → ι)
    (hf : Function.Injective f) (mask : Fin n → Bool) :
    (maskComputeProgram n f hf mask).length ≤ n+26*(n+1) := by
  have hm := maskFlipProgram_length n f mask
  have hz := zeroTest_length n
  simp only [maskComputeProgram,List.length_append,mappedZeroTest,mapProgram_length]
  omega

theorem maskedOracleCircuit_counts (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (mask : Fin n → Bool) (adj : Bool) :
    (maskedOracleCircuit (A := A) (B := B) n f hf mask adj).toQuery.matrixQueries=1 ∧
      (maskedOracleCircuit (A := A) (B := B) n f hf mask adj).toQuery.vectorQueries=0 ∧
      (maskedOracleCircuit (A := A) (B := B) n f hf mask adj).workGates ≤ 30*(n+26*(n+1)) := by
  have hc := TransducerCompiler.GateSynthesis.lowerProgram_length (maskComputeProgram n f hf mask)
  have hr := TransducerCompiler.GateSynthesis.lowerProgram_length (maskComputeProgram n f hf mask).reverse
  have hp := maskComputeProgram_length n f hf mask
  simp only [List.length_reverse] at hr
  constructor
  · simp only [maskedOracleCircuit,realProgramCircuit,ElementaryCircuit.toQuery_append,
      QueryCircuit.matrixQueries_append,(elementaryMacro_queries _).1,zero_add,add_zero]
    rfl
  constructor
  · simp only [maskedOracleCircuit,realProgramCircuit,ElementaryCircuit.toQuery_append,
      QueryCircuit.vectorQueries_append,(elementaryMacro_queries _).2,zero_add,add_zero]
    rfl
  · simp only [maskedOracleCircuit,ElementaryCircuit.workGates_append,realProgramCircuit,
      elementaryMacro_workGates,List.length_map,ElementaryCircuit.workGates]
    omega

/-- Every emitted matrix call is literally the designated single-flag port. -/
theorem maskedOracleCircuit_single_flag (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (mask : Fin n → Bool) (adj : Bool) (p : QueryPort A (ElementarySpace ι A)) (b : Bool)
    (h : ElementaryInstruction.matrixCall p b ∈ maskedOracleCircuit (B := B) n f hf mask adj) :
    p=singleFlagOraclePort A (f (smallTarget n)) ∧ b=adj := by
  simpa [maskedOracleCircuit,realProgramCircuit,elementaryMacro] using h

end OptimalQLS.GraphEncoding
