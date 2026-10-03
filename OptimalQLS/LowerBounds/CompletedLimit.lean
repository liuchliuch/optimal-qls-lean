import OptimalQLS.LowerBounds.CountableOutput
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Completed output converges without a termination assumption

Completed density matrices increase in the PSD order. Their bounded monotone
traces force operator-norm Cauchy convergence. The remaining mass is retained
as a separate failure flag, so nontermination is counted as failure.
-/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
namespace OptimalQLS.LowerBounds
open Matrix Filter QuantumChannelStein.TraceNorm
variable {D A O : Type*} [Fintype D] [DecidableEq D] [Fintype A] [DecidableEq A]
  [Fintype O] [DecidableEq O]

theorem HaltingProgram.completed_increment_positive (p : HaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (s : HaltingState D A) (hs : s.Positive) :
    ((p.run U s).completed - s.completed).PosSemidef := by
  have hd : s = ⟨s.completed, s.live⟩ := rfl
  rw [hd, p.run_decomposition]
  change (s.completed + (p.run U ⟨0, s.live⟩).completed - s.completed).PosSemidef
  have heq : s.completed + (p.run U ⟨0, s.live⟩).completed - s.completed = (p.run U ⟨0, s.live⟩).completed := by abel
  rw [heq]
  exact (p.run_positive U ⟨0, s.live⟩ ⟨Matrix.PosSemidef.zero, hs.2⟩).1

def CountableHaltingProgram.completedProbability (p : CountableHaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (s : HaltingState D A) (n : ℕ) : ℝ :=
  ((p.prefix n).run U s).completed.trace.re

theorem CountableHaltingProgram.completed_increment_positive (p : CountableHaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (s : HaltingState D A) (hs : s.Positive) {n m : ℕ} (hnm : n ≤ m) :
    (((p.prefix m).run U s).completed - ((p.prefix n).run U s).completed).PosSemidef := by
  obtain ⟨rest, hrest⟩ := p.prefix_isPrefix hnm
  rw [← hrest, HaltingProgram.run_append]
  exact HaltingProgram.completed_increment_positive rest U _ ((p.prefix n).run_positive U s hs)

theorem CountableHaltingProgram.completedProbability_monotone (p : CountableHaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (s : HaltingState D A) (hs : s.Positive) :
    Monotone (p.completedProbability U s) := by
  intro n m hnm
  have h := (p.completed_increment_positive U s hs hnm).trace_nonneg.1
  simpa [completedProbability, Matrix.trace_sub] using h

theorem CountableHaltingProgram.completedProbability_bddAbove (p : CountableHaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (s : HaltingState D A) (hs : s.Positive) :
    BddAbove (Set.range (p.completedProbability U s)) := by
  refine ⟨s.mass.re, ?_⟩
  rintro x ⟨n, rfl⟩
  have hn := ((p.prefix n).run_positive U s hs).2.trace_nonneg.1
  have ht := congrArg Complex.re ((p.prefix n).run_mass U s)
  dsimp only [HaltingState.mass] at ht
  simp only [Complex.add_re] at ht
  change ((p.prefix n).run U s).completed.trace.re ≤ s.completed.trace.re + s.live.trace.re
  norm_num at hn
  linarith

theorem CountableHaltingProgram.completed_cauchy (p : CountableHaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (s : HaltingState D A) (hs : s.Positive) :
    CauchySeq (fun n => ((p.prefix n).run U s).completed) := by
  let L := ⨆ n, p.completedProbability U s n
  have hmono := p.completedProbability_monotone U s hs
  have hbdd := p.completedProbability_bddAbove U s hs
  have hlim : Tendsto (p.completedProbability U s) atTop (𝓝 L) := tendsto_atTop_ciSup hmono hbdd
  apply cauchySeq_of_le_tendsto_0' (fun n => L - p.completedProbability U s n)
  · intro n m hnm
    rw [dist_eq_norm, norm_sub_rev]
    have hpos := p.completed_increment_positive U s hs hnm
    apply (opNorm_le_traceNorm _).trans
    rw [traceNorm_positive_eq_trace _ hpos, Matrix.trace_sub, Complex.sub_re]
    have hm : p.completedProbability U s m ≤ L := le_ciSup hbdd m
    exact sub_le_sub_right hm _
  · simpa using (tendsto_const_nhds (x := L)).sub hlim

def CountableHaltingProgram.completedLimit (p : CountableHaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (s : HaltingState D A) (hs : s.Positive) : Matrix D D ℂ :=
  Classical.choose (cauchySeq_tendsto_of_complete (p.completed_cauchy U s hs))

theorem CountableHaltingProgram.completedLimit_tendsto (p : CountableHaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (s : HaltingState D A) (hs : s.Positive) :
    Tendsto (fun n => ((p.prefix n).run U s).completed) atTop (𝓝 (p.completedLimit U s hs)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (p.completed_cauchy U s hs))

/-- Add the missing trace to the separate failure flag. -/
def failureCompletion (mass : ℂ) (X : Matrix D D ℂ) : Matrix (D ⊕ Unit) (D ⊕ Unit) ℂ :=
  Matrix.fromBlocks X 0 0 ((mass - X.trace) • (1 : Matrix Unit Unit ℂ))

theorem failureCompletion_continuous (mass : ℂ) : Continuous (failureCompletion (D := D) mass) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  cases i <;> cases j <;> simp only [failureCompletion, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  · fun_prop
  · fun_prop
  · fun_prop
  · simp only [Matrix.smul_apply, smul_eq_mul]
    exact ((continuous_const.sub matrixTrace_continuous).mul continuous_const)

def CountableHaltingProgram.abortPrefix (p : CountableHaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (s : HaltingState D A) (n : ℕ) : Matrix (D ⊕ Unit) (D ⊕ Unit) ℂ :=
  (abortChannel (D := D) (A := A)).apply ((p.prefix n).run U s).matrix

theorem CountableHaltingProgram.abortPrefix_eq (p : CountableHaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (s : HaltingState D A) (n : ℕ) :
    p.abortPrefix U s n = failureCompletion s.mass ((p.prefix n).run U s).completed := by
  have ht := (p.prefix n).run_mass U s
  have heq : ((p.prefix n).run U s).live.trace = s.mass - ((p.prefix n).run U s).completed.trace := by
    change ((p.prefix n).run U s).completed.trace + ((p.prefix n).run U s).live.trace = s.mass at ht
    linear_combination ht
  simp only [abortPrefix, HaltingState.matrix, abortChannel_apply, failureCompletion, heq]

/-- A total output semantics including nontermination as failure. -/
def CountableHaltingProgram.totalOutput (p : CountableHaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (s : HaltingState D A) (hs : s.Positive) : Matrix (D ⊕ Unit) (D ⊕ Unit) ℂ :=
  failureCompletion s.mass (p.completedLimit U s hs)

theorem CountableHaltingProgram.totalOutput_tendsto (p : CountableHaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (s : HaltingState D A) (hs : s.Positive) :
    Tendsto (p.abortPrefix U s) atTop (𝓝 (p.totalOutput U s hs)) := by
  have h := (failureCompletion_continuous s.mass).tendsto (p.completedLimit U s hs)
  convert h.comp (p.completedLimit_tendsto U s hs) using 1
  funext n
  exact p.abortPrefix_eq U s n

end OptimalQLS.LowerBounds
