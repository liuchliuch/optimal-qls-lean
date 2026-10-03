import OptimalQLS.LowerBounds.AbortHybrid

/-!
# Physical total outputs and a common finite prefix on finitely many inputs

This is the analytic prefix approximation needed before finite workspace
padding. It makes no termination assumption and includes every requested
original/paired input in one common cutoff.
-/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
namespace OptimalQLS.LowerBounds
open Matrix Filter
variable {D A O : Type*} [Fintype D] [DecidableEq D] [Fintype A] [DecidableEq A]
  [Fintype O] [DecidableEq O]

theorem matrixPosSemidef_isClosed : IsClosed {X : Matrix D D ℂ | X.PosSemidef} := by
  simp only [Matrix.posSemidef_iff_dotProduct_mulVec, Set.setOf_and, Set.setOf_forall]
  apply IsClosed.inter
  · exact isClosed_eq (by fun_prop) continuous_id
  · apply isClosed_iInter
    intro x
    apply isClosed_le continuous_const
    unfold dotProduct Matrix.mulVec
    fun_prop

theorem CountableHaltingProgram.totalOutput_positive (p : CountableHaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (s : HaltingState D A) (hs : s.Positive) :
    (p.totalOutput U s hs).PosSemidef := by
  apply matrixPosSemidef_isClosed.mem_of_tendsto (p.totalOutput_tendsto U s hs)
  exact Filter.Eventually.of_forall (fun n => (abortChannel (D := D) (A := A)).apply_positive
    (((p.prefix n).run U s).matrix_positive ((p.prefix n).run_positive U s hs)))

theorem CountableHaltingProgram.totalOutput_trace (p : CountableHaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (s : HaltingState D A) (hs : s.Positive) :
    (p.totalOutput U s hs).trace = s.mass := by
  simp [totalOutput, failureCompletion, trace_blockDiagonal]

theorem CountableHaltingProgram.prefix_traceDistance_tendsto_zero (p : CountableHaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (s : HaltingState D A) (hs : s.Positive) :
    Tendsto (fun n => traceDistance (p.abortPrefix U s n) (p.totalOutput U s hs)) atTop (𝓝 0) := by
  have h := traceDistance_continuous.tendsto (p.totalOutput U s hs, p.totalOutput U s hs)
  have hx := (p.totalOutput_tendsto U s hs).prodMk_nhds (tendsto_const_nhds (x := p.totalOutput U s hs))
  simpa using h.comp hx

/-- A single actual prefix length simultaneously approximates finitely many
concrete oracle executions, including all original and paired hard inputs. -/
theorem exists_common_finite_prefix {I : Type*} [Finite I]
    (program : I → CountableHaltingProgram O D A) (oracle : I → Matrix.unitaryGroup O ℂ)
    (initial : I → HaltingState D A) (hpositive : ∀ i, (initial i).Positive)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ cutoff : ℕ, ∀ i, ∀ n ≥ cutoff,
      traceDistance ((program i).abortPrefix (oracle i) (initial i) n)
        ((program i).totalOutput (oracle i) (initial i) (hpositive i)) < eta := by
  have hi (i : I) : ∀ᶠ n in atTop,
      traceDistance ((program i).abortPrefix (oracle i) (initial i) n)
        ((program i).totalOutput (oracle i) (initial i) (hpositive i)) < eta :=
    ((program i).prefix_traceDistance_tendsto_zero (oracle i) (initial i) (hpositive i)).eventually (gt_mem_nhds heta)
  have hall : ∀ᶠ n in atTop, ∀ i, traceDistance ((program i).abortPrefix (oracle i) (initial i) n)
      ((program i).totalOutput (oracle i) (initial i) (hpositive i)) < eta := eventually_all.mpr hi
  obtain ⟨cutoff, hcutoff⟩ := eventually_atTop.mp hall
  exact ⟨cutoff, fun i n hn => hcutoff n hn i⟩

end OptimalQLS.LowerBounds
