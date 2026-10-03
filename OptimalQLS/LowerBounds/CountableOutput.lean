import OptimalQLS.LowerBounds.CountableHalting

/-! Physical normalization and completion-independence of countable outputs. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
namespace OptimalQLS.LowerBounds
open Matrix Filter QuantumChannelStein.TraceNorm
variable {D A O : Type*} [Fintype D] [DecidableEq D] [Fintype A] [DecidableEq A]
  [Fintype O] [DecidableEq O]

theorem traceDistance_eq_zero_iff (X Y : Matrix D D ℂ) : traceDistance X Y = 0 ↔ X = Y := by
  constructor
  · intro h
    have hn := opNorm_le_traceNorm (X - Y)
    have ht : traceNorm (X - Y) = 0 := by unfold traceDistance at h; linarith
    rw [ht] at hn
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))
  · rintro rfl; exact traceDistance_self _

theorem matrixTrace_continuous : Continuous (fun X : Matrix D D ℂ => X.trace) := by
  unfold Matrix.trace
  fun_prop

theorem CountableHaltingProgram.output_positive (p : CountableHaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (F : FiniteChannel A D) (s : HaltingState D A)
    (hs : s.Positive) (hhalt : p.HaltsOn U s) : (p.output U F s hs hhalt).PosSemidef := by
  have hc : IsClosed {X : Matrix (D ⊕ Unit) (D ⊕ Unit) ℂ | X.PosSemidef} := by
    simp only [Matrix.posSemidef_iff_dotProduct_mulVec, Set.setOf_and, Set.setOf_forall]
    apply IsClosed.inter
    · exact isClosed_eq (by fun_prop) continuous_id
    · apply isClosed_iInter
      intro x
      apply isClosed_le continuous_const
      unfold dotProduct Matrix.mulVec
      fun_prop
  apply hc.mem_of_tendsto (p.output_limit U F s hs hhalt)
  apply Filter.Eventually.of_forall
  intro n
  exact (finishChannel F).apply_positive (((p.prefix n).run U s).matrix_positive
    ((p.prefix n).run_positive U s hs))

theorem CountableHaltingProgram.output_trace (p : CountableHaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (F : FiniteChannel A D) (s : HaltingState D A)
    (hs : s.Positive) (hhalt : p.HaltsOn U s) : (p.output U F s hs hhalt).trace = s.mass := by
  have hlim := (matrixTrace_continuous.tendsto _).comp (p.output_limit U F s hs hhalt)
  have heq : (fun n => (p.finiteOutput U F s n).trace) = fun _ => s.mass := by
    funext n
    simp [finiteOutput, HaltingProgram.output, FiniteChannel.trace_apply,
      HaltingState.matrix_trace, HaltingProgram.run_mass]
  change Tendsto (fun n => (p.finiteOutput U F s n).trace) atTop _ at hlim
  rw [heq] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

theorem HaltingProgram.finish_choice_distance (p : HaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (F G : FiniteChannel A D) (s : HaltingState D A)
    (hs : s.Positive) : traceDistance (p.output U F s) (p.output U G s) ≤
      2 * (p.run U s).live.trace.re := by
  have hF := p.output_truncation_distance p.length U F s hs
  have hG := p.output_truncation_distance p.length U G s hs
  simp only [List.take_length] at hF hG
  have htri := traceDistance_triangle (p.output U F s) (p.truncatedOutput p.length U s) (p.output U G s)
  rw [traceDistance_symm (p.truncatedOutput p.length U s)] at htri
  linarith

/-- The arbitrary query-free channel used to complete finite prefixes has no
influence on the true almost-surely terminating output. -/
theorem CountableHaltingProgram.output_independent_completion (p : CountableHaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (F G : FiniteChannel A D) (s : HaltingState D A)
    (hs : s.Positive) (hhalt : p.HaltsOn U s) : p.output U F s hs hhalt = p.output U G s hs hhalt := by
  apply (traceDistance_eq_zero_iff _ _).mp
  apply le_antisymm _ (traceDistance_nonneg _ _)
  have hlim := traceDistance_continuous.tendsto
    (p.output U F s hs hhalt, p.output U G s hs hhalt)
  have hout := (p.output_limit U F s hs hhalt).prodMk_nhds (p.output_limit U G s hs hhalt)
  have hz : Tendsto (fun n => 2 * p.liveProbability U s n) atTop (𝓝 0) := by
    simpa using hhalt.const_mul 2
  exact le_of_tendsto_of_tendsto (hlim.comp hout) hz (Filter.Eventually.of_forall
    (fun n => (p.prefix n).finish_choice_distance U F G s hs))

/-- Every round has a literal nonnegative query-occurrence Born probability. -/
theorem CountableHaltingProgram.liveProbability_nonneg (p : CountableHaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (s : HaltingState D A) (hs : s.Positive) (n : ℕ) :
    0 ≤ p.liveProbability U s n := ((p.prefix n).run_positive U s hs).2.trace_nonneg.1

/-- A resource bound expressed only in positive-probability query occurrences. -/
def CountableHaltingProgram.PointwiseQueryBound (p : CountableHaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (s : HaltingState D A) (q : ℕ) : Prop :=
  ∀ k, 0 < p.liveProbability U s k → k + 1 ≤ q

theorem CountableHaltingProgram.one_sided_hybrid_of_pointwise_bound (p : CountableHaltingProgram O D A)
    (q : ℕ) (U V : Matrix.unitaryGroup O ℂ) (F : FiniteChannel A D) (s : HaltingState D A)
    (hs : s.Positive) (hms : s.mass = 1) (hU : p.HaltsOn U s) (hV : p.HaltsOn V s)
    (hq : p.PointwiseQueryBound U s q) :
    traceDistance (p.output U F s hs hU) (p.output V F s hs hV) ≤
      3 * (q : ℝ) * ‖(U : Matrix O O ℂ) - (V : Matrix O O ℂ)‖ := by
  apply p.one_sided_halting_hybrid q U V F s hs hms hU hV
  have hn := p.liveProbability_nonneg U s hs q
  by_contra hne
  have hp : 0 < p.liveProbability U s q := lt_of_le_of_ne hn (Ne.symm hne)
  have := hq q hp
  omega

end OptimalQLS.LowerBounds
