import OptimalQLS.PolynomialTransform.DirtyAncilla.Ladder
import OptimalQLS.PolynomialTransform.DirtyAncilla.Wiring

/-! # Uniform borrowed-ladder interface for every control count -/
namespace OptimalQLS.PolynomialTransform.DirtyAncilla
open OptimalQLS.TransducerCompiler.BinaryClock

abbrev ManyWire (k : ℕ) := Fin k ⊕ (Fin (k-2) ⊕ Unit)
def manyTarget (k : ℕ) : ManyWire k := .inr (.inr ())
def allControls {k : ℕ} (b : ManyWire k → Bool) : Bool := decide (∀ i : Fin k, b (.inl i)=true)

def manyDirty : (k : ℕ) → Program (ManyWire k)
  | 0 => [.x (manyTarget 0)]
  | 1 => [.cx (.inl 0) (manyTarget 1) (by simp [manyTarget])]
  | 2 => [.ccx (.inl 0) (.inl 1) (manyTarget 2) (by simp [manyTarget]) (by simp [manyTarget])]
  | n+3 => dirtyControlledNot n

/-- All controls and all k−2 borrowed bits are exactly restored. -/
theorem manyDirty_run (k : ℕ) (b : ManyWire k → Bool) :
    run (manyDirty k) b=Function.update b (manyTarget k) (Bool.xor (b (manyTarget k)) (allControls b)) := by
  rcases k with _|_|_|n
  · simp [manyDirty,run,Gate.act,allControls]
  · simp [manyDirty,run,Gate.act,allControls,Fin.forall_fin_one]
  · have ha : allControls b=(b (.inl 0)&&b (.inl 1)) := by
      apply Bool.eq_iff_iff.mpr
      simp [allControls,Fin.forall_fin_two]
    simp [manyDirty,run,Gate.act,ha]
  · simpa only [manyDirty,target,manyTarget,prefixAnd_full,allControls,control] using dirtyControlledNot_run n b

theorem manyDirty_length (k : ℕ) : (manyDirty k).length ≤ 4*(k+1) := by
  rcases k with _|_|_|n
  · simp [manyDirty]
  · simp [manyDirty]
  · simp [manyDirty]
  · exact (dirtyControlledNot_length n).trans (by omega)

/-- Physical embedding into arbitrary spectator wires preserves exact target semantics. -/
theorem mapped_manyDirty_run {ι : Type*} [DecidableEq ι] (k : ℕ)
    (f : ManyWire k → ι) (hf : Function.Injective f) (b : ι → Bool) :
    run (mapProgram f hf (manyDirty k)) b = Function.update b (f (manyTarget k))
      (Bool.xor (b (f (manyTarget k))) (decide (∀ i : Fin k, b (f (.inl i))=true))) := by
  simpa only [allControls,Function.comp_def] using
    mapProgram_target f hf (manyDirty k) (manyTarget k)
      (fun x => Bool.xor (x (manyTarget k)) (allControls x)) (manyDirty_run k) b

end OptimalQLS.PolynomialTransform.DirtyAncilla
