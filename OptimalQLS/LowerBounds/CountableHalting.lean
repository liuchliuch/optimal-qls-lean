import OptimalQLS.LowerBounds.PointwiseQueryCost
import OptimalQLS.LowerBounds.TraceNormContinuity
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Countably many actual stopping rounds

The workspace and output registers are fixed finite types, while the number
of query rounds is unbounded. Almost-sure termination is the literal condition
that the trace of the live density tends to zero. Existence of the final
matrix limit is proved from that condition, not postulated as a hybrid bound.
-/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
namespace OptimalQLS.LowerBounds
open Matrix Filter QuantumChannelStein.TraceNorm
variable {D A O : Type*} [Fintype D] [DecidableEq D] [Fintype A] [DecidableEq A]
  [Fintype O] [DecidableEq O]

abbrev CountableHaltingProgram (O D A : Type*) [Fintype D] [Fintype A] [DecidableEq A] :=
  ℕ → HaltingRound O D A

def CountableHaltingProgram.prefix (p : CountableHaltingProgram O D A) : ℕ → HaltingProgram O D A
  | 0 => []
  | n + 1 => p.prefix n ++ [p n]

@[simp] theorem CountableHaltingProgram.prefix_length (p : CountableHaltingProgram O D A) (n : ℕ) :
    (p.prefix n).length = n := by induction n <;> simp_all [CountableHaltingProgram.prefix]

theorem CountableHaltingProgram.prefix_isPrefix (p : CountableHaltingProgram O D A) {n m : ℕ} (hnm : n ≤ m) :
    p.prefix n <+: p.prefix m := by
  induction hnm with
  | refl => exact List.prefix_refl _
  | @step m hnm ih => exact ih.trans ⟨[p m], rfl⟩

theorem CountableHaltingProgram.prefix_take (p : CountableHaltingProgram O D A) {n m : ℕ} (hnm : n ≤ m) :
    (p.prefix m).take n = p.prefix n := by
  have h := List.prefix_iff_eq_take.mp (p.prefix_isPrefix hnm)
  simpa using h.symm

def CountableHaltingProgram.liveProbability (p : CountableHaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (s : HaltingState D A) (n : ℕ) : ℝ :=
  ((p.prefix n).run U s).live.trace.re

/-- Ordinary almost-sure termination, in terms of actual live Born mass. -/
def CountableHaltingProgram.HaltsOn (p : CountableHaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (s : HaltingState D A) : Prop :=
  Tendsto (p.liveProbability U s) atTop (𝓝 0)

def CountableHaltingProgram.finiteOutput (p : CountableHaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (F : FiniteChannel A D) (s : HaltingState D A) (n : ℕ) :
    Matrix (D ⊕ Unit) (D ⊕ Unit) ℂ := (p.prefix n).output U F s

theorem CountableHaltingProgram.finiteOutput_cauchy_bound (p : CountableHaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (F : FiniteChannel A D) (s : HaltingState D A)
    (hs : s.Positive) (n m : ℕ) (hnm : n ≤ m) :
    dist (p.finiteOutput U F s n) (p.finiteOutput U F s m) ≤ 4 * p.liveProbability U s n := by
  have h₁ := (p.prefix n).output_truncation_distance n U F s hs
  have h₂ := (p.prefix m).output_truncation_distance n U F s hs
  have hn : (p.prefix n).take n = p.prefix n := p.prefix_take (le_refl n)
  have hm : (p.prefix m).take n = p.prefix n := p.prefix_take hnm
  have htrunc : (p.prefix m).truncatedOutput n U s = (p.prefix n).truncatedOutput n U s := by
    simp only [HaltingProgram.truncatedOutput, hn, hm]
  rw [hm, htrunc] at h₂
  rw [hn] at h₁
  have htri := traceDistance_triangle ((p.prefix n).output U F s) ((p.prefix n).truncatedOutput n U s) ((p.prefix m).output U F s)
  rw [traceDistance_symm ((p.prefix n).truncatedOutput n U s)] at htri
  have hnrm := opNorm_le_traceNorm (((p.prefix n).output U F s) - ((p.prefix m).output U F s))
  simp only [traceDistance] at h₁ h₂ htri
  rw [dist_eq_norm]
  dsimp only [finiteOutput, liveProbability]
  linarith

theorem CountableHaltingProgram.finiteOutput_cauchy (p : CountableHaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (F : FiniteChannel A D) (s : HaltingState D A)
    (hs : s.Positive) (hhalt : p.HaltsOn U s) : CauchySeq (p.finiteOutput U F s) := by
  apply cauchySeq_of_le_tendsto_0' (fun n => 4 * p.liveProbability U s n)
    (p.finiteOutput_cauchy_bound U F s hs)
  simpa using hhalt.const_mul 4

theorem CountableHaltingProgram.exists_output (p : CountableHaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (F : FiniteChannel A D) (s : HaltingState D A)
    (hs : s.Positive) (hhalt : p.HaltsOn U s) :
    ∃ out, Tendsto (p.finiteOutput U F s) atTop (𝓝 out) :=
  cauchySeq_tendsto_of_complete (p.finiteOutput_cauchy U F s hs hhalt)

/-- The actual final state, obtained as the proved limit of finite executions. -/
def CountableHaltingProgram.output (p : CountableHaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (F : FiniteChannel A D) (s : HaltingState D A)
    (hs : s.Positive) (hhalt : p.HaltsOn U s) : Matrix (D ⊕ Unit) (D ⊕ Unit) ℂ :=
  Classical.choose (p.exists_output U F s hs hhalt)

theorem CountableHaltingProgram.output_limit (p : CountableHaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (F : FiniteChannel A D) (s : HaltingState D A)
    (hs : s.Positive) (hhalt : p.HaltsOn U s) :
    Tendsto (p.finiteOutput U F s) atTop (𝓝 (p.output U F s hs hhalt)) :=
  Classical.choose_spec (p.exists_output U F s hs hhalt)

/-- Countably many rounds are allowed on the perturbed oracle. The sole
resource restriction is zero live Born probability after q original queries. -/
theorem CountableHaltingProgram.one_sided_halting_hybrid (p : CountableHaltingProgram O D A)
    (q : ℕ) (U V : Matrix.unitaryGroup O ℂ) (F : FiniteChannel A D) (s : HaltingState D A)
    (hs : s.Positive) (hms : s.mass = 1) (hU : p.HaltsOn U s) (hV : p.HaltsOn V s)
    (hq : p.liveProbability U s q = 0) :
    traceDistance (p.output U F s hs hU) (p.output V F s hs hV) ≤
      3 * (q : ℝ) * ‖(U : Matrix O O ℂ) - (V : Matrix O O ℂ)‖ := by
  have hlim := traceDistance_continuous.tendsto
    (p.output U F s hs hU, p.output V F s hs hV)
  have hout := (p.output_limit U F s hs hU).prodMk_nhds (p.output_limit V F s hs hV)
  have hbound (n : ℕ) : traceDistance (p.finiteOutput U F s n) (p.finiteOutput V F s n) ≤
      3 * (q : ℝ) * ‖(U : Matrix O O ℂ) - (V : Matrix O O ℂ)‖ := by
    apply (p.prefix n).one_sided_halting_hybrid q U V F s hs hms
    intro hlen
    have hqn : q ≤ n := by simpa using Nat.le_of_lt hlen
    rw [p.prefix_take hqn]
    exact hq
  exact le_of_tendsto (hlim.comp hout) (Filter.Eventually.of_forall hbound)

end OptimalQLS.LowerBounds
