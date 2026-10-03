import OptimalQLS.Preparation.CompilerAttachment.Frames

/-! # Actual emitted preparation resources and the physical qubit register -/
noncomputable section
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 700000
open scoped Classical
namespace OptimalQLS.Preparation.CompilerAttachment
open Matrix TransducerCompiler BinaryClock PolynomialTransform

theorem preparationExponent_pos {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ) :
    0<preparationExponent κ := by
  by_contra hn
  have hz : preparationExponent κ=0 := by omega
  have hb := (h.mainBudget_bounds).1
  have hk : mainBudget κ=1 := by
    change 2^preparationExponent κ=1
    rw [hz]
    rfl
  rw [hk] at hb
  norm_num at hb
  linarith [h.kappa_ge_two]

theorem preparationCompiler_resources {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ) :
    (preparationCompiler κ ŝ).workCalls=mainBudget κ ∧
    (preparationCompiler κ ŝ).firstCalls=mainBudget κ ∧
    (preparationCompiler κ ŝ).secondCalls=reflectionBudget κ ŝ ∧
    (preparationCompiler κ ŝ).auxGates≤1110*mainBudget κ := by
  have hc := complete_exact_counts h.layout 0 (preparationPeriod κ ŝ)
    h.layout_D₁_dyadic h.layout_D₂_dyadic
  have ho := compile_exact_counts h.layout
  exact ⟨hc.1,hc.2.1.trans (ho.2.1.symm.trans h.layout_exact_counts.2.1),
    hc.2.2.trans (ho.2.2.symm.trans h.layout_exact_counts.2.2),synthesized_aux_bound _ _ _⟩

/-- The numerical bound applies only after a gate-count inequality for the actual list
has been proved. It includes the source-query adapter and graph-label initialization. -/
theorem actual_gate_bound (a n g : ℕ) {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ)
    (hg : g ≤ 436789*(a+1)*mainBudget κ+11222*(n+1)*reflectionBudget κ ŝ+2401) :
    (g : ℝ) < 200000000000000*κ*(a+1)+700000000000*(κ/s)*(n+1) := by
  have hgr : (g : ℝ) ≤ 436789*((a : ℝ)+1)*(mainBudget κ : ℝ)+
      11222*((n : ℝ)+1)*(reflectionBudget κ ŝ : ℝ)+2401 := by exact_mod_cast hg
  have hk := mul_lt_mul_of_pos_left h.mainBudget_bounds.2
    (by positivity : 0<(436789*((a : ℝ)+1)))
  have hr := mul_lt_mul_of_pos_left h.reflectionBudget_scale_bound
    (by positivity : 0<(11222*((n : ℝ)+1)))
  have hs : 0<s := by linarith [h.scale_ge_one]
  have hks : 0<κ/s := div_pos h.kappa_pos hs
  have ha : 2≤κ*((a : ℝ)+1) := by nlinarith [h.kappa_ge_two,(Nat.cast_nonneg a : 0≤(a : ℝ))]
  have hn : 0<(κ/s)*((n : ℝ)+1) := mul_pos hks (by positivity)
  nlinarith

/-- Three new bits beyond the existing compiler register. All a original signal
and n data qubits are physical; no active-dimension shortcut is taken. -/
theorem physical_qubit_bound (a n : ℕ) {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ) :
    Fintype.card (Physical a n (preparationExponent κ))=
      2^(n+a+2*preparationExponent κ+13) ∧
    n+a+2*preparationExponent κ+13≤n+a+2*Nat.log2 ⌈κ⌉₊+69 := by
  refine ⟨physical_card a n _,?_⟩
  have hq := appendixA2_qubits h
  simp only [auxiliaryQubits] at hq
  omega

end OptimalQLS.Preparation.CompilerAttachment
