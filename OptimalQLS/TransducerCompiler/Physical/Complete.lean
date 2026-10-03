import OptimalQLS.TransducerCompiler.Physical.Input

/-! # Full physical fixed-accuracy compiler for the supplied controlled work list

The circuit is selected before all oracle values, public vectors and catalysts.
Every charged gate is an actual at-most-two-wire tensor unitary. Both query
ports expose the literal original argument bits and one computed control bit.
-/
noncomputable section
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
open scoped Classical
namespace OptimalQLS.TransducerCompiler.Physical
open Matrix BinaryClock PolynomialTransform Refinement.CostedExecution

def PhysicallySafe {m ℓ : ℕ} (hℓ : 0<ℓ) (out : Circuit m ℓ) : Prop :=
  (∀ g,NamedInstruction.gate g∈out→IsTwoLocal (coordinates m ℓ) (gateEval m ℓ hℓ g)) ∧
  (∀ p adj,NamedInstruction.matrixCall p adj∈out→
    Nonempty (LiteralQueryPlacement (Equiv.refl (Bits m)) (coordinates m ℓ) p)) ∧
  (∀ p adj,NamedInstruction.vectorCall p adj∈out→
    Nonempty (LiteralQueryPlacement (Equiv.refl (Bits m)) (coordinates m ℓ) p))

theorem compile_physicallySafe (m ℓ : ℕ) (hℓ : 0<ℓ) (work : WorkCircuit m) (c : SynthCircuit ℓ) :
    PhysicallySafe hℓ (compile m ℓ work c) :=
  ⟨fun g _=>gate_local m ℓ hℓ g,compile_matrix_placement m ℓ work c,
    compile_vector_placement m ℓ work c⟩

/-- Lemma 2.8 with the supplied controlled work circuit literally expanded.
The only implementation premise is equality of that supplied list to controlled
S°, as the manuscript explicitly assumes. Its uniform transduction/error
relation is proved by the compiler, never supplied as a certificate. -/
theorem lemma28_physical (m : ℕ) {ε W L₁ L₂ : ℝ}
    (h : FixedAccuracyParameters ε W L₁ L₂) (work : WorkCircuit m) :
    ∃ out : Circuit m (accuracyExponent ε W),
      strictCircuit out ∧ PhysicallySafe (accuracyExponent_pos h) out ∧
      (out.toQuery (gateEval m _ (accuracyExponent_pos h))).matrixQueries=accuracyBudget ε L₁ ∧
      (out.toQuery (gateEval m _ (accuracyExponent_pos h))).vectorQueries=accuracyBudget ε L₂ ∧
      ((out.toQuery (gateEval m _ (accuracyExponent_pos h))).matrixQueries : ℝ)<32*L₁/ε^2 ∧
      ((out.toQuery (gateEval m _ (accuracyExponent_pos h))).vectorQueries : ℝ)<32*L₂/ε^2 ∧
      out.workGates≤(5910+work.length)*accuracyBudget ε W ∧
      (out.workGates : ℝ)<32*(5910+(work.length : ℝ))*W/ε^2 ∧
      ∀ (S : Matrix.unitaryGroup (Base (Bits m)) ℂ) (U₁ U₂ : Matrix.unitaryGroup (Bits m) ℂ)
        (ξ τ v₀ v₁ v₂ : Bits m → ℂ),
        ControlledWork S work →
        S.val*ᵥbundle ξ v₀ (U₁.val*ᵥv₁) (U₂.val*ᵥv₂)=bundle τ v₀ v₁ v₂ →
        energy v₀+energy v₁+energy v₂≤W → energy v₁≤L₁ → energy v₂≤L₂ →
        ‖WithLp.toLp 2 (((out.toQuery (gateEval m _ (accuracyExponent_pos h))).eval U₁ U₂).val*ᵥ
          publicInput m _ ξ-publicInput m _ τ)‖<ε := by
  obtain ⟨c,hw,hf,hs,hfb,hsb,ha,hg,he⟩:=lemma28_complete (n := Bits m) h
  let out:=compile m (accuracyExponent ε W) work c
  have hc:=compile_counts m _ (accuracyExponent_pos h) work c
  have h₁:c.firstCalls≤accuracyBudget ε W := hf.trans_le h.firstBudget_le_workBudget
  have h₂:c.secondCalls≤accuracyBudget ε W := hs.trans_le h.secondBudget_le_workBudget
  have hb:=compile_gate_bound m _ (accuracyExponent_pos h) work c (accuracyBudget ε W) ha hw h₁ h₂
  refine ⟨out,compile_strict m _ work c,compile_physicallySafe m _ (accuracyExponent_pos h) work c,
    hc.1.trans hf,hc.2.1.trans hs,?_,?_,hb,?_,?_⟩
  · rw [hc.1]; exact hfb
  · rw [hc.2.1]; exact hsb
  · calc
      (out.workGates : ℝ)≤(5910+(work.length : ℝ))*(accuracyBudget ε W : ℝ) := by exact_mod_cast hb
      _ < (5910+(work.length : ℝ))*(32*W/ε^2) :=
        mul_lt_mul_of_pos_left h.workBudget_bounds.2 (by positivity)
      _ = 32*(5910+(work.length : ℝ))*W/ε^2 := by ring
  · intro S U₁ U₂ ξ τ v₀ v₁ v₂ hwork hS hW hL₁ hL₂
    rw [publicInput_eq m _ h.layout ξ,publicInput_eq m _ h.layout τ]
    rw [show out=compile m (accuracyExponent ε W) work c from rfl,
      compile_error_eq m _ (accuracyExponent_pos h) S work hwork c U₁ U₂]
    exact he S U₁ U₂ ξ τ v₀ v₁ v₂ hS hW hL₁ hL₂

end OptimalQLS.TransducerCompiler.Physical
