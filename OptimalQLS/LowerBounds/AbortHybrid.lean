import OptimalQLS.LowerBounds.CompletedLimit

/-! One-sided hybrid including residual nontermination as a failure flag. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
namespace OptimalQLS.LowerBounds
open Matrix Filter
variable {D A O : Type*} [Fintype D] [DecidableEq D] [Fintype A] [DecidableEq A]
  [Fintype O] [DecidableEq O]

def HaltingProgram.terminalAbort (p : HaltingProgram O D A) (U : Matrix.unitaryGroup O ℂ)
    (s : HaltingState D A) : Matrix (D ⊕ Unit) (D ⊕ Unit) ℂ :=
  (abortChannel (D := D) (A := A)).apply (p.run U s).matrix

theorem HaltingProgram.terminalAbort_decomposition (p : HaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (Y : Matrix D D ℂ) (X : Matrix A A ℂ) :
    p.terminalAbort U ⟨Y, X⟩ = Matrix.fromBlocks Y 0 0 (0 : Matrix Unit Unit ℂ) + p.terminalAbort U ⟨0, X⟩ := by
  rw [terminalAbort, p.run_decomposition]
  simp [HaltingState.addCompleted, HaltingState.matrix, abortChannel_apply, terminalAbort, Matrix.fromBlocks_add]

theorem HaltingProgram.terminalAbort_initial_distance (p : HaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (Y : Matrix D D ℂ) (X : Matrix A A ℂ) (hX : X.PosSemidef) :
    traceDistance (p.terminalAbort U ⟨Y, X⟩)
      ((abortChannel (D := D) (A := A)).apply (Matrix.fromBlocks Y 0 0 X)) ≤ X.trace.re := by
  let G : Matrix (D ⊕ Unit) (D ⊕ Unit) ℂ := Matrix.fromBlocks Y 0 0 0
  let R := p.terminalAbort U ⟨0, X⟩
  let S := (abortChannel (D := D) (A := A)).apply (Matrix.fromBlocks 0 0 0 X)
  have hR : R.PosSemidef := (abortChannel (D := D) (A := A)).apply_positive
    ((p.run U ⟨0, X⟩).matrix_positive (p.run_positive U ⟨0, X⟩ ⟨Matrix.PosSemidef.zero, hX⟩))
  have hS : S.PosSemidef := (abortChannel (D := D) (A := A)).apply_positive (blockDiagonal_positive Matrix.PosSemidef.zero hX)
  have htR : R.trace.re = X.trace.re := by
    dsimp only [R, terminalAbort]
    rw [FiniteChannel.trace_apply, HaltingState.matrix_trace, p.run_mass]
    simp [HaltingState.mass]
  have htS : S.trace.re = X.trace.re := by simp [S, FiniteChannel.trace_apply, trace_blockDiagonal]
  have h := traceDistance_common_positive_residual G R S hR hS X.trace.re htR htS
  rw [p.terminalAbort_decomposition]
  simpa [G, R, S, abortChannel_apply, Matrix.fromBlocks_add] using h

theorem HaltingProgram.terminalAbort_truncation_distance (p : HaltingProgram O D A) (q : ℕ)
    (U : Matrix.unitaryGroup O ℂ) (s : HaltingState D A) (hs : s.Positive) :
    traceDistance (p.terminalAbort U s) (p.truncatedOutput q U s) ≤ (HaltingProgram.run (p.take q) U s).live.trace.re := by
  let t := HaltingProgram.run (p.take q) U s
  have ht : t.Positive := HaltingProgram.run_positive (p.take q) U s hs
  have hsplit : p.run U s = HaltingProgram.run (p.drop q) U t := by
    calc
      p.run U s = HaltingProgram.run (p.take q ++ p.drop q) U s := by rw [List.take_append_drop]
      _ = _ := HaltingProgram.run_append (p.take q) (p.drop q) U s
  change traceDistance ((abortChannel (D := D) (A := A)).apply (p.run U s).matrix)
    ((abortChannel (D := D) (A := A)).apply t.matrix) ≤ t.live.trace.re
  rw [hsplit]
  exact HaltingProgram.terminalAbort_initial_distance (p.drop q) U t.completed t.live ht.2

theorem HaltingProgram.terminalAbort_hybrid (p : HaltingProgram O D A) (U V : Matrix.unitaryGroup O ℂ)
    (s : HaltingState D A) (hs : s.Positive) (hms : s.mass = 1) :
    traceDistance (p.terminalAbort U s) (p.terminalAbort V s) ≤
      (p.length : ℝ) * ‖(U : Matrix O O ℂ) - (V : Matrix O O ℂ)‖ := by
  exact ((abortChannel (D := D) (A := A)).traceDistance_contract _ _).trans (p.run_same_initial_hybrid U V s hs hms)

theorem HaltingProgram.one_sided_abort_hybrid (p : HaltingProgram O D A) (q : ℕ)
    (U V : Matrix.unitaryGroup O ℂ) (s : HaltingState D A)
    (hs : s.Positive) (hms : s.mass = 1) (hq : p.OriginalQueryBound U s q) :
    traceDistance (p.terminalAbort U s) (p.terminalAbort V s) ≤
      3 * (q : ℝ) * ‖(U : Matrix O O ℂ) - (V : Matrix O O ℂ)‖ := by
  let delta := ‖(U : Matrix O O ℂ) - (V : Matrix O O ℂ)‖
  have hd : 0 ≤ delta := norm_nonneg _
  by_cases hlen : q < p.length
  · have hzero := hq hlen
    have hold := p.terminalAbort_truncation_distance q U s hs
    rw [hzero] at hold
    have hnew := p.terminalAbort_truncation_distance q V s hs
    have htrunc := p.truncatedOutput_hybrid q U V s hs hms
    have habort := bounded_observable_difference (abortProjection (D := D))
      (p.truncatedOutput q V s) (p.truncatedOutput q U s) abortProjection_norm_le_one
    have hprob (W : Matrix.unitaryGroup O ℂ) :
        (abortProjection * p.truncatedOutput q W s).trace.re =
          (HaltingProgram.run (p.take q) W s).live.trace.re := by
      exact abortProjection_probability _ _
    rw [hprob V, hprob U, hzero, sub_zero, traceDistance_symm] at habort
    have hlive : (HaltingProgram.run (p.take q) V s).live.trace.re ≤ 2 * (q : ℝ) * delta :=
      (le_abs_self _).trans (habort.trans (by dsimp [delta]; linarith))
    have htri₁ := traceDistance_triangle (p.terminalAbort U s) (p.truncatedOutput q U s) (p.terminalAbort V s)
    have htri₂ := traceDistance_triangle (p.truncatedOutput q U s) (p.truncatedOutput q V s) (p.terminalAbort V s)
    rw [traceDistance_symm (p.truncatedOutput q V s) (p.terminalAbort V s)] at htri₂
    change traceDistance (p.terminalAbort U s) (p.terminalAbort V s) ≤ 3 * (q : ℝ) * delta
    change traceDistance (p.truncatedOutput q U s) (p.truncatedOutput q V s) ≤ (q : ℝ) * delta at htrunc
    linarith
  · have hlen' : (p.length : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.le_of_not_gt hlen
    have h := (p.terminalAbort_hybrid U V s hs hms).trans (mul_le_mul_of_nonneg_right hlen' hd)
    change traceDistance (p.terminalAbort U s) (p.terminalAbort V s) ≤ 3 * (q : ℝ) * delta
    change traceDistance (p.terminalAbort U s) (p.terminalAbort V s) ≤ (q : ℝ) * delta at h
    nlinarith [mul_nonneg (Nat.cast_nonneg q) hd]

/-- The limiting one-sided stopping theorem has no almost-sure halting premise.
Any residual nontermination mass is part of the separate failure flag. -/
theorem CountableHaltingProgram.totalOutput_one_sided_hybrid (p : CountableHaltingProgram O D A)
    (q : ℕ) (U V : Matrix.unitaryGroup O ℂ) (s : HaltingState D A)
    (hs : s.Positive) (hms : s.mass = 1) (hq : p.PointwiseQueryBound U s q) :
    traceDistance (p.totalOutput U s hs) (p.totalOutput V s hs) ≤
      3 * (q : ℝ) * ‖(U : Matrix O O ℂ) - (V : Matrix O O ℂ)‖ := by
  have hzero : p.liveProbability U s q = 0 := by
    have hn := p.liveProbability_nonneg U s hs q
    by_contra hne
    have hp : 0 < p.liveProbability U s q := lt_of_le_of_ne hn (Ne.symm hne)
    have := hq q hp
    omega
  have hlim := traceDistance_continuous.tendsto (p.totalOutput U s hs, p.totalOutput V s hs)
  have hout := (p.totalOutput_tendsto U s hs).prodMk_nhds (p.totalOutput_tendsto V s hs)
  have hbound (n : ℕ) : traceDistance (p.abortPrefix U s n) (p.abortPrefix V s n) ≤
      3 * (q : ℝ) * ‖(U : Matrix O O ℂ) - (V : Matrix O O ℂ)‖ := by
    apply (p.prefix n).one_sided_abort_hybrid q U V s hs hms
    intro hlen
    have hqn : q ≤ n := by simpa using Nat.le_of_lt hlen
    rw [p.prefix_take hqn]
    exact hzero
  exact le_of_tendsto (hlim.comp hout) (Filter.Eventually.of_forall hbound)

end OptimalQLS.LowerBounds
