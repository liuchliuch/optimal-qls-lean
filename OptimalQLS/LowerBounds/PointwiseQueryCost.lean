import OptimalQLS.LowerBounds.HaltingHybrid

/-!
# Literal pointwise query cost from positive Born occurrence probabilities

A query is reachable exactly when its live density matrix has positive trace.
The maximum of the reachable occurrence indices is an actual finite maximum,
not an assumed worst-case bound or an abstract hardness certificate.
-/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
variable {D A O : Type*} [Fintype D] [DecidableEq D] [Fintype A] [DecidableEq A]
  [Fintype O] [DecidableEq O]

def HaltingProgram.queryOccurrenceProbability (p : HaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (s : HaltingState D A) (k : ℕ) : ℝ :=
  if k < p.length then (HaltingProgram.run (p.take k) U s).live.trace.re else 0

def HaltingProgram.pointwiseQueryCost (p : HaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (s : HaltingState D A) : ℕ :=
  (Finset.range p.length).sup (fun k => if 0 < p.queryOccurrenceProbability U s k then k + 1 else 0)

theorem HaltingProgram.queryOccurrenceProbability_nonneg (p : HaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (s : HaltingState D A) (hs : s.Positive) (k : ℕ) :
    0 ≤ p.queryOccurrenceProbability U s k := by
  unfold queryOccurrenceProbability
  split
  · have h := (HaltingProgram.run_positive (p.take k) U s hs).2.trace_nonneg
    exact h.1
  · rfl

theorem HaltingProgram.reachable_query_le_cost (p : HaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (s : HaltingState D A) (k : ℕ)
    (hk : k < p.length) (hp : 0 < p.queryOccurrenceProbability U s k) :
    k + 1 ≤ p.pointwiseQueryCost U s := by
  have h := Finset.le_sup (f := fun j => if 0 < p.queryOccurrenceProbability U s j then j + 1 else 0)
    (Finset.mem_range.mpr hk)
  simpa [pointwiseQueryCost, hp] using h

theorem HaltingProgram.pointwiseQueryCost_le_length (p : HaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (s : HaltingState D A) :
    p.pointwiseQueryCost U s ≤ p.length := by
  apply Finset.sup_le
  intro k hk
  split
  · exact Finset.mem_range.mp hk
  · exact Nat.zero_le _

theorem HaltingProgram.originalQueryBound_of_cost_le (p : HaltingProgram O D A)
    (U : Matrix.unitaryGroup O ℂ) (s : HaltingState D A) (hs : s.Positive) (q : ℕ)
    (hq : p.pointwiseQueryCost U s ≤ q) : p.OriginalQueryBound U s q := by
  intro hlen
  have hn := p.queryOccurrenceProbability_nonneg U s hs q
  have hz : p.queryOccurrenceProbability U s q = 0 := by
    by_contra hne
    have hp : 0 < p.queryOccurrenceProbability U s q := lt_of_le_of_ne hn (Ne.symm hne)
    have hcost := p.reachable_query_le_cost U s q hlen hp
    omega
  simpa [queryOccurrenceProbability, hlen] using hz

/-- No query-budget premise: the bound uses the actual maximum reachable
query occurrence on the original oracle, defined from its Born probabilities. -/
theorem HaltingProgram.pointwise_one_sided_hybrid (p : HaltingProgram O D A)
    (U V : Matrix.unitaryGroup O ℂ) (F : FiniteChannel A D) (s : HaltingState D A)
    (hs : s.Positive) (hms : s.mass = 1) :
    traceDistance (p.output U F s) (p.output V F s) ≤
      3 * (p.pointwiseQueryCost U s : ℝ) * ‖(U : Matrix O O ℂ) - (V : Matrix O O ℂ)‖ :=
  p.one_sided_halting_hybrid _ U V F s hs hms
    (p.originalQueryBound_of_cost_le U s hs _ (le_refl _))

end OptimalQLS.LowerBounds
