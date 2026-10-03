import OptimalQLS.LowerBounds.TraceDistance

/-! Equivalence and continuity for the genuine trace-square-root norm. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix QuantumChannelStein.TraceNorm
variable {D : Type*} [Fintype D] [DecidableEq D]

theorem norm_trace_le_card_mul_opNorm (X : Matrix D D ℂ) : ‖X.trace‖ ≤ Fintype.card D * ‖X‖ := by
  calc
    _ ≤ ∑ i, ‖X i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : D, ‖X‖ := Finset.sum_le_sum (fun i _ => norm_entry_le_opNorm X i i)
    _ = _ := by simp

theorem traceNorm_le_card_mul_opNorm (X : Matrix D D ℂ) : traceNorm X ≤ Fintype.card D * ‖X‖ := by
  obtain ⟨U, hU⟩ := exists_unitary_trace_eq X
  rw [← hU]
  apply (Complex.re_le_norm _).trans
  apply (norm_trace_le_card_mul_opNorm _).trans
  gcongr
  exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_of_le_one_left (norm_nonneg X) (unitary_opNorm_le_one U))

theorem opNorm_le_traceNorm (X : Matrix D D ℂ) : ‖X‖ ≤ traceNorm X := by
  obtain ⟨U, V, hX⟩ := exists_svd_sqrt_eigenvalues X
  let H := Matrix.isHermitian_conjTranspose_mul_self X
  let sigma : D → ℂ := fun i => Real.sqrt (H.eigenvalues i)
  have hd : ‖Matrix.diagonal sigma‖ ≤ traceNorm X := by
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (traceNorm_nonneg X)).mpr
    intro i
    change ‖(Real.sqrt (H.eigenvalues i) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), traceNorm_eq_sum_sqrt_eigenvalues]
    exact Finset.single_le_sum (fun j _ => Real.sqrt_nonneg _) (Finset.mem_univ i)
  have heq : X = (U : Matrix D D ℂ) * Matrix.diagonal sigma * (V : Matrix D D ℂ).conjTranspose := hX
  calc
    ‖X‖ = ‖(U : Matrix D D ℂ) * Matrix.diagonal sigma * (V : Matrix D D ℂ).conjTranspose‖ := by rw [← heq]
    _ ≤ ‖(U : Matrix D D ℂ) * Matrix.diagonal sigma‖ * ‖(V : Matrix D D ℂ).conjTranspose‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖(U : Matrix D D ℂ)‖ * ‖Matrix.diagonal sigma‖) * ‖(V : Matrix D D ℂ).conjTranspose‖ := by gcongr; exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 * traceNorm X) * 1 := by
      have ht := traceNorm_nonneg X
      rw [Matrix.l2_opNorm_conjTranspose]
      exact mul_le_mul (mul_le_mul (unitary_opNorm_le_one U) hd (norm_nonneg _) (by norm_num))
        (unitary_opNorm_le_one V) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem traceNorm_sub_abs_le (X Y : Matrix D D ℂ) : |traceNorm X - traceNorm Y| ≤ traceNorm (X - Y) := by
  have hX := traceNorm_add_le (X - Y) Y
  have hY := traceNorm_add_le (Y - X) X
  have heq : Y - X = -(X - Y) := by abel
  simp only [sub_add_cancel] at hX hY
  rw [heq, traceNorm_negative] at hY
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem traceNorm_continuous : Continuous (traceNorm (n := D)) := by
  have h : LipschitzWith ⟨Fintype.card D, by positivity⟩ (traceNorm (n := D)) := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro X Y
    simpa only [Real.dist_eq, dist_eq_norm, NNReal.coe_mk] using
      (traceNorm_sub_abs_le X Y).trans (traceNorm_le_card_mul_opNorm (X - Y))
  exact h.continuous

theorem traceDistance_continuous : Continuous (fun xy : Matrix D D ℂ × Matrix D D ℂ => traceDistance xy.1 xy.2) := by
  exact (traceNorm_continuous.comp (continuous_fst.sub continuous_snd)).div_const 2

end OptimalQLS.LowerBounds
