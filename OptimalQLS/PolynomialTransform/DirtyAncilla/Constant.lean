import OptimalQLS.PolynomialTransform.DirtyAncilla.Balanced

/-! # Constant-scratch multi-controlled NOT for every number of controls -/
namespace OptimalQLS.PolynomialTransform.DirtyAncilla
open OptimalQLS.TransducerCompiler.BinaryClock

theorem balanced_split (n : ℕ) : (n+1)/2+n/2=n := by omega

def balancedWireEquiv (n : ℕ) : SmallWire ((n+1)/2+n/2) ≃ SmallWire n :=
  Equiv.sumCongr (finCongr (balanced_split n)) (Equiv.refl (Fin 2))

/-- One target and one borrowed bit suffice, irrespective of the control count. -/
def constantAncillaNot (n : ℕ) : Program (SmallWire n) :=
  mapProgram (balancedWireEquiv n) (balancedWireEquiv n).injective
    (balancedProgram ((n+1)/2) (n/2) (by omega) (by omega))

theorem forall_fin_cast {m n : ℕ} (h : m=n) (b : Fin n → Bool) :
    decide (∀ i : Fin m, b (Fin.cast h i)=true)=decide (∀ i : Fin n, b i=true) := by
  subst n
  rfl

/-- Actual target-only semantics; the borrowed bit may begin in either state. -/
theorem constantAncillaNot_run (n : ℕ) (b : SmallWire n → Bool) :
    run (constantAncillaNot n) b=Function.update b (smallTarget n)
      (Bool.xor (b (smallTarget n)) (decide (∀ i : Fin n, b (.inl i)=true))) := by
  have h := mapProgram_target (balancedWireEquiv n) (balancedWireEquiv n).injective
    (balancedProgram ((n+1)/2) (n/2) (by omega) (by omega))
    (smallTarget ((n+1)/2+n/2))
    (fun x => Bool.xor (x (smallTarget ((n+1)/2+n/2)))
      (decide (∀ i : Fin ((n+1)/2+n/2), x (.inl i)=true)))
    (balancedProgram_run ((n+1)/2) (n/2) (by omega) (by omega)) b
  simpa only [constantAncillaNot, balancedWireEquiv, smallTarget, Function.comp_apply,
    Equiv.sumCongr_apply, Equiv.refl_apply, Sum.map_inl, Sum.map_inr, finCongr_apply,
    forall_fin_cast (balanced_split n) (fun i => b (.inl i))] using h

theorem constantAncillaNot_length (n : ℕ) : (constantAncillaNot n).length ≤ 24*(n+1) := by
  rw [constantAncillaNot,mapProgram_length]
  simpa only [balanced_split] using balancedProgram_length ((n+1)/2) (n/2) (by omega) (by omega)

end OptimalQLS.PolynomialTransform.DirtyAncilla
