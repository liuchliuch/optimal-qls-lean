import OptimalQLS.PolynomialTransform.DirtyAncilla.ControlledPhase
import OptimalQLS.PolynomialTransform.CleanEmbedding

/-! # Zero-tested arbitrary one-qubit unitaries with constant scratch -/
noncomputable section
namespace OptimalQLS.Preparation
open Matrix OptimalQLS.TransducerCompiler BinaryClock
open OptimalQLS.PolynomialTransform DirtyAncilla
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A genuine two-qubit controlled gate, first bit control and second bit target. -/
def controlledTargetUnitary (U : Matrix.unitaryGroup Bool ℂ) : Matrix.unitaryGroup (Bool × Bool) ℂ :=
  rewireUnitary (Equiv.prodComm Bool Bool) (controlledOn (fun b : Bool => b) U)

theorem controlledTarget_entries (U : Matrix.unitaryGroup Bool ℂ) (a b c d : Bool) :
    (controlledTargetUnitary U).val (a,b) (c,d) =
      if a=c then (if c then U.val b d else if b=d then 1 else 0) else 0 := by
  cases a <;> cases c <;> simp [controlledTargetUnitary,rewireUnitary,controlledOn,
    Matrix.blockDiagonal_apply,Matrix.one_apply]

theorem pairWiring_target_update (f t : ι) (hft : f≠t) (z : Bool) (b : ι → Bool) (y : Bool) :
    pairWiring f t hft ((b f,y),(z,fun i => b i.val)) = (z,Function.update b t y) := by
  apply Prod.ext
  · rfl
  · funext i
    by_cases hf : i=f <;> by_cases ht : i=t <;> simp_all [pairWiring,Function.update,Ne.symm hft]

/-- Exact basis expansion of a physically placed controlled one-qubit gate. -/
theorem controlledTarget_basis (f t : ι) (hft : f≠t)
    (U : Matrix.unitaryGroup Bool ℂ) (z : Bool) (b : ι → Bool) :
    ((PhaseGate.pair f t hft (controlledTargetUnitary U)).eval).val *ᵥ Pi.single (z,b) 1 =
      ∑ y : Bool, (if b f then U.val y (b t) else if y=b t then 1 else 0) •
        (Pi.single (z,Function.update b t y) 1 : GateSynthesis.Space ι → ℂ) := by
  change (GateSynthesis.placeHom (pairWiring f t hft) (controlledTargetUnitary U)).val*ᵥ_ = _
  have hi : pairWiring f t hft ((b f,b t),(z,fun i => b i.val))=(z,b) := by
    exact (pairWiring f t hft).apply_symm_apply (z,b)
  conv_lhs => rw [← hi]
  rw [placeHom_basis_sum,Fintype.sum_prod_type]
  simp only [controlledTarget_entries]
  rw [Finset.sum_eq_single (b f)]
  · simp only [ite_true]
    apply Finset.sum_congr rfl
    intro y _
    rw [pairWiring_target_update]
  · intro j _ hj
    simp [hj]
  · simp

def zeroControlledTarget (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (t : ι) (hft : f (smallTarget n)≠t) (U : Matrix.unitaryGroup Bool ℂ) : List (PhaseGate ι) :=
  (GateSynthesis.lowerProgram (mappedZeroTest n f hf)).map PhaseGate.real ++
    [.pair (f (smallTarget n)) t hft (controlledTargetUnitary U)] ++
    (GateSynthesis.lowerProgram (mappedZeroTest n f hf).reverse).map PhaseGate.real

theorem zeroControlledTarget_length (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (t : ι) (hft : f (smallTarget n)≠t) (U : Matrix.unitaryGroup Bool ℂ) :
    (zeroControlledTarget n f hf t hft U).length ≤ 781*(n+1) := by
  have h := GateSynthesis.lowerProgram_length (mappedZeroTest n f hf)
  have h' := GateSynthesis.lowerProgram_length (mappedZeroTest n f hf).reverse
  have hz := zeroTest_length n
  simp only [List.length_reverse,mappedZeroTest,mapProgram_length] at h h'
  simp only [zeroControlledTarget,mappedZeroTest,List.length_append,List.length_map,List.length_cons,List.length_nil]
  omega

/-- Changing only an untested target commutes with the entire exact zero-test program. -/
theorem mappedZeroTest_target_update (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (t : ι) (hft : f (smallTarget n)≠t) (ht : ∀ i : Fin n, f (.inl i)≠t)
    (b : ι → Bool) (y : Bool) :
    run (mappedZeroTest n f hf) (Function.update b t y) =
      Function.update (run (mappedZeroTest n f hf) b) t y := by
  have hc : (∀ i : Fin n, (Function.update b t y) (f (.inl i))=false) ↔
      (∀ i : Fin n, b (f (.inl i))=false) := by simp [Function.update_of_ne,ht]
  rw [mappedZeroTest_run,mappedZeroTest_run]
  simp only [Function.update_of_ne hft,hc]
  funext i
  by_cases h₁ : i=f (smallTarget n) <;> by_cases h₂ : i=t <;>
    simp_all [Function.update]

/-- Exact coherent action of the macro on every computational input with its
zero-test flag clean. The borrowed bit and all spectators are unrestricted. -/
theorem zeroControlledTarget_basis (n : ℕ) (f : SmallWire n → ι) (hf : Function.Injective f)
    (t : ι) (hft : f (smallTarget n)≠t) (ht : ∀ i : Fin n, f (.inl i)≠t)
    (U : Matrix.unitaryGroup Bool ℂ) (b : ι → Bool) (hb : b (f (smallTarget n))=false) :
    (phaseEval (zeroControlledTarget n f hf t hft U)).val*ᵥPi.single (false,b) 1 =
      ∑ y : Bool,
        (if decide (∀ i : Fin n, b (f (.inl i))=false) then U.val y (b t)
          else if y=b t then 1 else 0) •
        (Pi.single (false,Function.update b t y) 1 : GateSynthesis.Space ι → ℂ) := by
  simp only [zeroControlledTarget,phaseEval_append,phaseEval_real,phaseEval,
    PhaseGate.eval,one_mul,Submonoid.coe_mul,← Matrix.mulVec_mulVec]
  rw [GateSynthesis.lowerProgram_basis]
  change (GateSynthesis.eval (GateSynthesis.lowerProgram (mappedZeroTest n f hf).reverse)).val*ᵥ
    ((PhaseGate.pair (f (smallTarget n)) t hft (controlledTargetUnitary U)).eval.val*ᵥ
      Pi.single (false,run (mappedZeroTest n f hf) b) 1) = _
  rw [controlledTarget_basis,Matrix.mulVec_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [Matrix.mulVec_smul,GateSynthesis.lowerProgram_basis,
    ← mappedZeroTest_target_update n f hf t hft ht,run_reverse_run]
  congr 1
  simp [mappedZeroTest_run,hb,Ne.symm hft]

end OptimalQLS.Preparation
