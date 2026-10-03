import OptimalQLS.LowerBounds.HaltingProcess

/-!
# One-sided stopping-time hybrid for actual finite halting processes

All states, query ports, instruments, truncations and residuals in this file
are the concrete matrices defined in the preceding modules. The bound depends
only on the query budget under the original oracle. The factor 3, rather than
the sharp factor 2, comes from the general bounded-observable trace inequality.
-/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix QuantumChannelStein.TraceNorm
variable {D A O : Type*} [Fintype D] [DecidableEq D] [Fintype A] [DecidableEq A]
  [Fintype O] [DecidableEq O]

theorem unitary_conjugation_contract (U : Matrix.unitaryGroup D ℂ) (X Y : Matrix D D ℂ) :
    traceDistance ((U : Matrix D D ℂ) * X * (U : Matrix D D ℂ).conjTranspose)
      ((U : Matrix D D ℂ) * Y * (U : Matrix D D ℂ).conjTranspose) ≤ traceDistance X Y := by
  have h := traceNorm_sandwich_le (U : Matrix D D ℂ) (X - Y) (U : Matrix D D ℂ).conjTranspose
  rw [Matrix.l2_opNorm_conjTranspose] at h
  have hU := unitary_opNorm_le_one U
  have hXY := traceNorm_nonneg (X - Y)
  have hb : traceNorm ((U : Matrix D D ℂ) * (X - Y) * (U : Matrix D D ℂ).conjTranspose) ≤ traceNorm (X - Y) :=
    h.trans (by calc
      _ ≤ 1 * traceNorm (X - Y) * 1 := by gcongr
      _ = _ := by ring)
  unfold traceDistance
  simpa only [Matrix.mul_sub, Matrix.sub_mul] using
    div_le_div_of_nonneg_right hb (by norm_num : (0 : ℝ) ≤ 2)

theorem unitary_mixed_input_bound (U V : Matrix.unitaryGroup D ℂ) (X Y : Matrix D D ℂ)
    (hY : Y.PosSemidef) (ht : Y.trace = 1) :
    traceDistance ((U : Matrix D D ℂ) * X * (U : Matrix D D ℂ).conjTranspose)
      ((V : Matrix D D ℂ) * Y * (V : Matrix D D ℂ).conjTranspose) ≤
      traceDistance X Y + ‖(U : Matrix D D ℂ) - (V : Matrix D D ℂ)‖ := by
  exact (traceDistance_triangle _ ((U : Matrix D D ℂ) * Y * (U : Matrix D D ℂ).conjTranspose) _).trans
    (add_le_add (unitary_conjugation_contract U X Y) (unitary_query_traceDistance U V Y hY ht))

theorem HaltingRound.fullQuery_difference_norm_le (r : HaltingRound O D A) (U V : Matrix.unitaryGroup O ℂ) :
    ‖(r.fullQuery U : Matrix (D ⊕ A) (D ⊕ A) ℂ) - (r.fullQuery V : Matrix (D ⊕ A) (D ⊕ A) ℂ)‖ ≤
      ‖(U : Matrix O O ℂ) - (V : Matrix O O ℂ)‖ := by
  change ‖Matrix.fromBlocks 1 0 0 (r.query U : Matrix A A ℂ) -
    Matrix.fromBlocks 1 0 0 (r.query V : Matrix A A ℂ)‖ ≤ _
  have heq : Matrix.fromBlocks (1 : Matrix D D ℂ) 0 0 (r.query U : Matrix A A ℂ) -
      Matrix.fromBlocks 1 0 0 (r.query V : Matrix A A ℂ) =
      Matrix.fromBlocks 0 0 0 ((r.query U : Matrix A A ℂ) - (r.query V : Matrix A A ℂ)) := by
    ext i j
    cases i <;> cases j <;> simp
  rw [heq]
  simp only [blockDiagonal_norm, norm_zero, max_eq_right (norm_nonneg _)]
  exact queryPort_adjoint_difference_norm_le r.port r.adjoint U V

theorem HaltingRound.traceDistance_bound (r : HaltingRound O D A) (U V : Matrix.unitaryGroup O ℂ)
    (s t : HaltingState D A) (ht : t.Positive) (hmt : t.mass = 1) :
    traceDistance (r.apply U s).matrix (r.apply V t).matrix ≤
      traceDistance s.matrix t.matrix + ‖(U : Matrix O O ℂ) - (V : Matrix O O ℂ)‖ := by
  rw [r.apply_matrix, r.apply_matrix]
  apply (r.instrument.channel.traceDistance_contract _ _).trans
  exact (unitary_mixed_input_bound (r.fullQuery U) (r.fullQuery V) s.matrix t.matrix
    (t.matrix_positive ht) (t.matrix_trace.trans hmt)).trans
    (add_le_add_right (r.fullQuery_difference_norm_le U V) _)

theorem HaltingProgram.run_cons (r : HaltingRound O D A) (p : HaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (s : HaltingState D A) :
    HaltingProgram.run (r :: p) U s = p.run U (r.apply U s) := rfl

theorem HaltingProgram.run_hybrid (p : HaltingProgram O D A) (U V : Matrix.unitaryGroup O ℂ)
    (s t : HaltingState D A) (ht : t.Positive) (hmt : t.mass = 1) :
    traceDistance (p.run U s).matrix (p.run V t).matrix ≤
      traceDistance s.matrix t.matrix + (p.length : ℝ) * ‖(U : Matrix O O ℂ) - (V : Matrix O O ℂ)‖ := by
  induction p generalizing s t with
  | nil => simp [run]
  | cons r rest ih =>
    have h := ih (r.apply U s) (r.apply V t) (r.apply_positive V t ht) ((r.apply_mass V t).trans hmt)
    have hr := r.traceDistance_bound U V s t ht hmt
    simp only [HaltingProgram.run_cons]
    calc
      _ ≤ traceDistance (r.apply U s).matrix (r.apply V t).matrix + (rest.length : ℝ) * ‖(U : Matrix O O ℂ) - (V : Matrix O O ℂ)‖ := h
      _ ≤ (traceDistance s.matrix t.matrix + ‖(U : Matrix O O ℂ) - (V : Matrix O O ℂ)‖) + (rest.length : ℝ) * ‖(U : Matrix O O ℂ) - (V : Matrix O O ℂ)‖ := add_le_add_left hr _
      _ = _ := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring

theorem HaltingProgram.run_same_initial_hybrid (p : HaltingProgram O D A) (U V : Matrix.unitaryGroup O ℂ)
    (s : HaltingState D A) (hs : s.Positive) (hms : s.mass = 1) :
    traceDistance (p.run U s).matrix (p.run V s).matrix ≤
      (p.length : ℝ) * ‖(U : Matrix O O ℂ) - (V : Matrix O O ℂ)‖ := by
  simpa using p.run_hybrid U V s s hs hms

theorem HaltingProgram.truncatedOutput_hybrid (p : HaltingProgram O D A) (q : ℕ) (U V : Matrix.unitaryGroup O ℂ)
    (s : HaltingState D A) (hs : s.Positive) (hms : s.mass = 1) :
    traceDistance (p.truncatedOutput q U s) (p.truncatedOutput q V s) ≤
      (q : ℝ) * ‖(U : Matrix O O ℂ) - (V : Matrix O O ℂ)‖ := by
  apply ((abortChannel (D := D) (A := A)).traceDistance_contract _ _).trans
  apply (HaltingProgram.run_same_initial_hybrid (p.take q) U V s hs hms).trans
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast List.length_take_le q p) (norm_nonneg _)

theorem HaltingProgram.output_hybrid (p : HaltingProgram O D A) (U V : Matrix.unitaryGroup O ℂ)
    (F : FiniteChannel A D) (s : HaltingState D A) (hs : s.Positive) (hms : s.mass = 1) :
    traceDistance (p.output U F s) (p.output V F s) ≤
      (p.length : ℝ) * ‖(U : Matrix O O ℂ) - (V : Matrix O O ℂ)‖ := by
  exact ((finishChannel F).traceDistance_contract _ _).trans (p.run_same_initial_hybrid U V s hs hms)

/-- No positive Born mass reaches query q+1 on the original oracle. If the
program has at most q rounds, this condition is automatically satisfied. -/
def HaltingProgram.OriginalQueryBound (p : HaltingProgram O D A) (U : Matrix.unitaryGroup O ℂ)
    (s : HaltingState D A) (q : ℕ) : Prop :=
  q < p.length → (HaltingProgram.run (p.take q) U s).live.trace.re = 0

/-- A one-sided hybrid: no query cap under V is assumed. The only cap is
zero actual live Born probability before query q+1 under U. -/
theorem HaltingProgram.one_sided_halting_hybrid (p : HaltingProgram O D A) (q : ℕ)
    (U V : Matrix.unitaryGroup O ℂ) (F : FiniteChannel A D) (s : HaltingState D A)
    (hs : s.Positive) (hms : s.mass = 1) (hq : p.OriginalQueryBound U s q) :
    traceDistance (p.output U F s) (p.output V F s) ≤
      3 * (q : ℝ) * ‖(U : Matrix O O ℂ) - (V : Matrix O O ℂ)‖ := by
  let delta := ‖(U : Matrix O O ℂ) - (V : Matrix O O ℂ)‖
  have hd : 0 ≤ delta := norm_nonneg _
  by_cases hlen : q < p.length
  · have hzero := hq hlen
    have hold := p.output_truncation_distance q U F s hs
    rw [hzero] at hold
    have hnew := p.output_truncation_distance q V F s hs
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
    have htri₁ := traceDistance_triangle (p.output U F s) (p.truncatedOutput q U s) (p.output V F s)
    have htri₂ := traceDistance_triangle (p.truncatedOutput q U s) (p.truncatedOutput q V s) (p.output V F s)
    rw [traceDistance_symm (p.truncatedOutput q V s) (p.output V F s)] at htri₂
    change traceDistance (p.output U F s) (p.output V F s) ≤ 3 * (q : ℝ) * delta
    change traceDistance (p.truncatedOutput q U s) (p.truncatedOutput q V s) ≤ (q : ℝ) * delta at htrunc
    linarith
  · have hlen' : (p.length : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.le_of_not_gt hlen
    have h := (p.output_hybrid U V F s hs hms).trans (mul_le_mul_of_nonneg_right hlen' hd)
    change traceDistance (p.output U F s) (p.output V F s) ≤ 3 * (q : ℝ) * delta
    change traceDistance (p.output U F s) (p.output V F s) ≤ (q : ℝ) * delta at h
    nlinarith [mul_nonneg (Nat.cast_nonneg q) hd]

end OptimalQLS.LowerBounds
