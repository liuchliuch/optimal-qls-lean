import OptimalQLS.PolynomialTransform.DirtyAncilla.Constant
import OptimalQLS.TransducerCompiler.GateSynthesis

/-! # Linear-size zero test with two scratch bits and elementary lowering -/
noncomputable section
namespace OptimalQLS.PolynomialTransform.DirtyAncilla
open OptimalQLS.TransducerCompiler.BinaryClock
open OptimalQLS.TransducerCompiler Matrix

variable {ι : Type*} [DecidableEq ι]

theorem flipList_run (l : List ι) (hl : l.Nodup) (b : ι → Bool) (j : ι) :
    run (l.map Gate.x) b j = if j ∈ l then !(b j) else b j := by
  induction l generalizing b with
  | nil => simp [run]
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, run_cons]
    rw [ih hl.2]
    by_cases hji : j=i
    · subst j
      simp [hl.1,Gate.act]
    · simp [hji,Gate.act,Function.update_apply]

def flipControls (n : ℕ) : Program (SmallWire n) :=
  (List.ofFn (fun i : Fin n => (Sum.inl i : SmallWire n))).map Gate.x

def negateControls {n : ℕ} (b : SmallWire n → Bool) : SmallWire n → Bool
  | .inl i => !(b (.inl i))
  | .inr i => b (.inr i)

theorem flipControls_run (n : ℕ) (b : SmallWire n → Bool) :
    run (flipControls n) b=negateControls b := by
  ext j
  rw [flipControls,flipList_run]
  · cases j <;> simp [List.mem_ofFn,negateControls]
  · exact List.nodup_ofFn.mpr Sum.inl_injective

@[simp] theorem negateControls_twice {n : ℕ} (b : SmallWire n → Bool) :
    negateControls (negateControls b)=b := by
  ext j; cases j <;> simp [negateControls]

theorem negateControls_update {n : ℕ} (b : SmallWire n → Bool) (v : Bool) :
    negateControls (Function.update b (smallTarget n) v)=
      Function.update (negateControls b) (smallTarget n) v := by
  ext j; cases j <;> simp [negateControls,smallTarget,Function.update_apply]

def zeroTest (n : ℕ) : Program (SmallWire n) :=
  flipControls n ++ constantAncillaNot n ++ flipControls n

/-- Literal reversible zero-test semantics, including arbitrary dirty input. -/
theorem zeroTest_run (n : ℕ) (b : SmallWire n → Bool) :
    run (zeroTest n) b=Function.update b (smallTarget n)
      (Bool.xor (b (smallTarget n)) (decide (∀ i : Fin n, b (.inl i)=false))) := by
  simp only [zeroTest,run_append,flipControls_run,constantAncillaNot_run]
  rw [negateControls_update,negateControls_twice]
  simp [negateControls,smallTarget]

theorem zeroTest_length (n : ℕ) : (zeroTest n).length ≤ 26*(n+1) := by
  have h := constantAncillaNot_length n
  simp only [zeroTest,List.length_append,flipControls,List.length_map,List.length_ofFn]
  omega

/-- Actual one- and two-qubit implementation with one additional clean synthesis bit. -/
def elementaryZeroTest (n : ℕ) := GateSynthesis.lowerProgram (zeroTest n)

theorem elementaryZeroTest_length (n : ℕ) : (elementaryZeroTest n).length ≤ 390*(n+1) := by
  exact (GateSynthesis.lowerProgram_length _).trans (by have h := zeroTest_length n; omega)

theorem elementaryZeroTest_basis (n : ℕ) (b : SmallWire n → Bool) :
    (GateSynthesis.eval (elementaryZeroTest n)).val *ᵥ Pi.single (false,b) (1 : ℂ)=
      Pi.single (false,Function.update b (smallTarget n)
        (Bool.xor (b (smallTarget n)) (decide (∀ i : Fin n, b (.inl i)=false)))) 1 := by
  rw [elementaryZeroTest,GateSynthesis.lowerProgram_basis,zeroTest_run]

theorem elementaryZeroTest_arity (n : ℕ) (g : GateSynthesis.LowerGate (SmallWire n)) (_hg : g ∈ elementaryZeroTest n) : g.arity ≤ 2 :=
  GateSynthesis.LowerGate.arity_le_two g

end OptimalQLS.PolynomialTransform.DirtyAncilla
