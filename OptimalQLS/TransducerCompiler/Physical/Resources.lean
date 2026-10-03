import OptimalQLS.TransducerCompiler.Physical.Error

/-! Bounds for the emitted list and its literal binary workspace. -/
noncomputable section
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
open scoped Classical
namespace OptimalQLS.TransducerCompiler.Physical
open Matrix BinaryClock PolynomialTransform

theorem accuracyExponent_pos {ε W L₁ L₂ : ℝ} (h : FixedAccuracyParameters ε W L₁ L₂) :
    0<accuracyExponent ε W := by
  by_contra hn
  have hz : accuracyExponent ε W=0 := Nat.eq_zero_of_not_pos hn
  have hb:=h.workBudget_bounds.1
  change 16*W/ε^2≤((2^accuracyExponent ε W : ℕ) : ℝ) at hb
  rw [hz] at hb
  norm_num only [pow_zero,Nat.cast_one] at hb
  have hsq:=sq_pos_of_pos h.epsilon_pos
  have ht:16*W≤ε^2 := by simpa using (div_le_iff₀ hsq).mp hb
  have he:ε^2<1 := by nlinarith only [h.epsilon_pos,h.epsilon_lt_one]
  nlinarith only [h.work_ge_one,ht,he]

theorem compile_gate_bound (m ℓ : ℕ) (hℓ : 0<ℓ) (work : WorkCircuit m)
    (c : SynthCircuit ℓ) (K : ℕ) (ha : c.auxGates≤1110*K)
    (hw : c.workCalls=K) (h₁ : c.firstCalls≤K) (h₂ : c.secondCalls≤K) :
    (compile m ℓ work c).workGates≤(5910+work.length)*K := by
  have hb:=(compile_counts m ℓ hℓ work c).2.2
  rw [hw] at hb
  nlinarith only [hb,ha,Nat.mul_le_mul_left 2400 h₁,Nat.mul_le_mul_left 2400 h₂]

theorem space_card (m ℓ : ℕ) : Fintype.card (Space m ℓ)=2^(m+2*ℓ+6) := by
  rw [show Fintype.card (Space m ℓ)=Fintype.card (SynthSpace (Bits m) ℓ)*Fintype.card PhaseScratch from Fintype.card_prod _ _]
  rw [synthSpace_card]
  simp only [Bits,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,PhaseScratch,
    Fintype.card_prod,auxiliaryQubits,pow_add,pow_mul]
  ring

theorem accuracy_qubits {ε W L₁ L₂ : ℝ} (h : FixedAccuracyParameters ε W L₁ L₂) (m : ℕ) :
    m+2*accuracyExponent ε W+6≤
      m+2*Nat.log2 ⌈W⌉₊+2*powerTwoCeilExponent (16/ε^2)+8 := by
  have hb:=lemma28_qubits h
  simp only [auxiliaryQubits] at hb
  omega

end OptimalQLS.TransducerCompiler.Physical
