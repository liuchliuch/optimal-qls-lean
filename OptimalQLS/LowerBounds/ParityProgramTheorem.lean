import OptimalQLS.LowerBounds.QuantumCompleted
import OptimalQLS.LowerBounds.VariableMatrixLowerBound
import OptimalQLS.LowerBounds.Physical.HistoryBitCircuit

/-!
# Lemma 6.6 for an unbounded operational quantum program

The output flag is interpreted as the returned bit. Completed output mass
alone counts toward correctness, so a nonterminating run is never credited
with a correct answer. Strict success greater than one half on every input
gives a common finite prefix with the same property. Its actual Kraus paths
and the literal XOR oracle then supply the polynomial-method lower bound.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace OptimalQLS.LowerBounds
open Matrix Filter
universe u v r

/-- Probability of the indicated returned bit in a possibly subnormalized
completed output. The existing instruction's Boolean output tag is the bit. -/
def returnedBitProbability {d : ℕ} (bit : Bool)
    (X : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ) : ℝ :=
  ∑ i : Fin d, (X (if bit then Sum.inl i else Sum.inr i)
    (if bit then Sum.inl i else Sum.inr i)).re

theorem returnedBitProbability_continuous {d : ℕ} (bit : Bool) :
    Continuous (returnedBitProbability (d := d) bit) := by
  unfold returnedBitProbability
  fun_prop

theorem returnedBitProbability_sum {d : ℕ} {I : Type*} [Fintype I]
    (bit : Bool) (X : I → Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ) :
    returnedBitProbability bit (∑ i, X i) = ∑ i, returnedBitProbability bit (X i) := by
  simp only [returnedBitProbability, Matrix.sum_apply, Complex.re_sum]
  exact Finset.sum_comm

theorem returnedBitProbability_flag {d : ℕ} (bit flag : Bool) (psi : Fin d → ℂ) :
    returnedBitProbability bit
      (flagInjection flag * pureDensity psi * (flagInjection flag).conjTranspose) =
      if flag = bit then bornMass psi else 0 := by
  rw [flagInjection_conjugation]
  cases bit <;> cases flag <;>
    simp [returnedBitProbability, bornMass_eq_trace, Matrix.trace, Matrix.diag]

variable {A : Type u} {B : Type v} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] {d w : ℕ} {Node : ℕ → Type r}

/-- The completed-output probability equals the sum of the literal Born
weights of precisely the completed terminal paths returning that bit. -/
theorem FiniteOracleProgram.completedBitProbability_eq_sum
    (tree : FiniteOracleProgram A B d w) (path : VariableQueryPath A B w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (bit : Bool) :
    returnedBitProbability bit (tree.completedDensity UA Ub (path.state UA Ub)) =
      ∑ k : tree.Terminal, if tree.terminalAbortFlag k then 0 else
        if tree.terminalSuccess k = bit then (tree.terminalPath path k).bornWeight UA Ub else 0 := by
  induction tree with
  | output flag aborted =>
    cases aborted with
    | false =>
      simpa only [FiniteOracleProgram.completedDensity, Bool.false_eq_true,
        if_false, Terminal, terminalAbortFlag, terminalSuccess, terminalPath,
        Fintype.sum_unique, VariableQueryPath.bornWeight] using
          returnedBitProbability_flag bit flag (path.state UA Ub)
    | true =>
      simp [FiniteOracleProgram.completedDensity, returnedBitProbability,
        Terminal, terminalAbortFlag]
  | matrixQuery port adj next ih => exact ih (.matrixQuery port adj path)
  | vectorQuery port adj next ih => exact ih (.vectorQuery port adj path)
  | instrument rank dims K hn next ih =>
    change returnedBitProbability bit (∑ i, (next i).completedDensity UA Ub
      (K i *ᵥ path.state UA Ub)) =
      ∑ k : (i : Fin rank) × (next i).Terminal,
        if (next k.1).terminalAbortFlag k.2 then 0 else
          if (next k.1).terminalSuccess k.2 = bit then
            ((next k.1).terminalPath (.work (K k.1) path) k.2).bornWeight UA Ub else 0
    rw [returnedBitProbability_sum, Fintype.sum_sigma]
    exact Finset.sum_congr rfl (fun i _ => ih i (.work (K i) path))

/-- Completed output zero contributes +1, completed output one contributes
-1, and an unfinished prefix contributes zero to the decision bias. -/
def FiniteOracleProgram.parityDecisionWeight (tree : FiniteOracleProgram A B d w)
    (k : tree.Terminal) : ℝ :=
  if tree.terminalAbortFlag k then 0 else boolSign (tree.terminalSuccess k)

theorem FiniteOracleProgram.parityDecisionWeight_bound (tree : FiniteOracleProgram A B d w)
    (k : tree.Terminal) : |tree.parityDecisionWeight k| ≤ 1 := by
  unfold parityDecisionWeight
  cases tree.terminalAbortFlag k <;> cases tree.terminalSuccess k <;>
    norm_num [boolSign]

/-- Strict correct-output probability, without any halting assumption,
implies the signed bias needed by the actual path polynomial proof. -/
theorem FiniteOracleProgram.parityDecisionBias_positive {m : ℕ}
    (tree : FiniteOracleProgram A B d w) (UA : Matrix.unitaryGroup A ℂ)
    (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ)
    (hpsi : ‖WithLp.toLp 2 psi‖ = 1) (z : BitString m)
    (hcorrect : 1 / 2 < returnedBitProbability (xorFold (List.ofFn z))
      (tree.completedDensity UA Ub psi)) :
    0 < paritySign z * ∑ k : tree.Terminal,
      tree.parityDecisionWeight k * (tree.terminalPath (.initial psi) k).bornWeight UA Ub := by
  classical
  let probability := fun k : tree.Terminal =>
    (tree.terminalPath (.initial psi) k).bornWeight UA Ub
  let correct := fun k : tree.Terminal => if tree.terminalAbortFlag k then (0 : ℝ) else
    if tree.terminalSuccess k = xorFold (List.ofFn z) then probability k else 0
  have hmass : (∑ k, probability k) = 1 := by
    dsimp only [probability]
    rw [tree.terminalBorn_sum, bornMass_eq_norm_sq, hpsi]
    norm_num
  have hcorrect' : 1 / 2 < ∑ k, correct k := by
    have heq := tree.completedBitProbability_eq_sum (.initial psi) UA Ub (xorFold (List.ofFn z))
    change returnedBitProbability _ (tree.completedDensity UA Ub psi) = ∑ k, correct k at heq
    exact heq ▸ hcorrect
  have hpoint (k : tree.Terminal) : 2 * correct k - probability k ≤
      paritySign z * (tree.parityDecisionWeight k * probability k) := by
    have hp := (tree.terminalPath (.initial psi) k).bornWeight_nonneg UA Ub
    change 0 ≤ probability k at hp
    rw [← boolSign_xorFold_ofFn z]
    dsimp only [correct, parityDecisionWeight]
    cases tree.terminalAbortFlag k <;> cases tree.terminalSuccess k <;>
      cases xorFold (List.ofFn z) <;> simp [boolSign] <;> linarith
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hpoint k)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hmass, ← Finset.mul_sum] at hs
  exact lt_of_lt_of_le (by linarith [hcorrect']) hs

/-- General operational wrapper for any explicitly evaluated degree-one
oracle. This is an internal assembly lemma; the bit-oracle endpoint below
proves and discharges both polynomial hypotheses from its literal matrix. -/
theorem QuantumProgram.parity_hard_run_of_polynomial_oracle {m : ℕ}
    (program : QuantumProgram A B d Node) (out : Fin d)
    (P : Matrix A A (InputPolynomial m)) (hdegree : MatrixDegreeLE P 1)
    (UA : BitString m → Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (heval : ∀ z, evalMatrix z P = (UA z : Matrix A A ℂ))
    (node : Node w) (psi : Fin w → ℂ) (hpsi : ‖WithLp.toLp 2 psi‖ = 1)
    (hcorrect : ∀ z : BitString m, 1 / 2 <
      returnedBitProbability (xorFold (List.ofFn z))
        (program.completedLimit out (UA z) Ub node psi)) :
    ∃ (z : BitString m) (fuel : ℕ) (k : (program.unroll out fuel node).Terminal),
      0 < ((program.unroll out fuel node).terminalPath (.initial psi) k).bornWeight (UA z) Ub ∧
        m ≤ 2 * ((program.unroll out fuel node).terminalPath (.initial psi) k).matrixQueries := by
  classical
  have hevent (z : BitString m) : ∀ᶠ fuel in atTop,
      1 / 2 < returnedBitProbability (xorFold (List.ofFn z))
        ((program.unroll out fuel node).completedDensity (UA z) Ub psi) := by
    have ht := ((returnedBitProbability_continuous (d := d) (xorFold (List.ofFn z))).tendsto
      (program.completedLimit out (UA z) Ub node psi)).comp
        (program.completedLimit_tendsto out (UA z) Ub node psi)
    exact ht.eventually (lt_mem_nhds (hcorrect z))
  obtain ⟨fuel, hfuel⟩ := (eventually_all.mpr hevent).exists
  let tree := program.unroll out fuel node
  have hmass (z : BitString m) (s : Finset tree.Terminal) :
      (∑ k ∈ s, (tree.terminalPath (.initial psi) k).bornWeight (UA z) Ub) ≤ 1 := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun k _ _ => (tree.terminalPath (.initial psi) k).bornWeight_nonneg (UA z) Ub)).trans
    rw [tree.terminalBorn_sum, bornMass_eq_norm_sq, hpsi]
    norm_num
  obtain ⟨z, k, hborn, hqueries⟩ := countable_variable_matrix_hard_run P hdegree UA Ub heval
    (fun _ : tree.Terminal => d) (tree.terminalPath (.initial psi)) tree.parityDecisionWeight
    tree.parityDecisionWeight_bound hmass (fun z => by
      rw [countableVariableBias, tsum_fintype]
      exact tree.parityDecisionBias_positive (UA z) Ub psi hpsi z (hfuel z))
  exact ⟨z, fuel, k, hborn, hqueries⟩

/-- The full matrix of the ordinary XOR oracle, as literal entry polynomials. -/
def standardBitPolynomial (m : ℕ) :
    Matrix (Physical.BitBasis m) (Physical.BitBasis m) (InputPolynomial m) :=
  fun row col => if row.1 = col.1 then gatedXPolynomial (some col.1) row.2 col.2 else 0

theorem standardBitPolynomial_degree (m : ℕ) : MatrixDegreeLE (standardBitPolynomial m) 1 := by
  intro row col
  unfold standardBitPolynomial
  split_ifs
  · exact gatedXPolynomial_degree _ _ _
  · simp

theorem standardBitPolynomial_eval {m : ℕ} (z : BitString m) :
    evalMatrix z (standardBitPolynomial m) = (Physical.standardBitOracle z).val := by
  ext row col
  have hentry := congrFun (Physical.standardBitOracle_basis z col.1 col.2) row
  simp [Matrix.mulVec, dotProduct, Pi.single_apply] at hentry
  rw [hentry]
  by_cases h : row.1 = col.1
  · simp [evalMatrix, standardBitPolynomial, h, gatedXPolynomial_eval, labelBit,
      Prod.ext_iff, eq_comm]
  · simp [evalMatrix, standardBitPolynomial, h, Prod.ext_iff, Ne.symm h]

/-- The exact source correctness premise: on each Boolean input the actual
completed probability of returning its XOR is strictly greater than 1/2.
There is no conditioning on termination or lower bound on a uniform margin. -/
def QuantumProgram.ComputesParity {m : ℕ}
    (program : QuantumProgram (Physical.BitBasis m) B d Node) (out : Fin d)
    (Ub : Matrix.unitaryGroup B ℂ) (node : Node w) (psi : Fin w → ℂ) : Prop :=
  ∀ z : BitString m, 1 / 2 < returnedBitProbability (xorFold (List.ofFn z))
    (program.completedLimit out (Physical.standardBitOracle z) Ub node psi)

/-- Lemma 6.6. One original Boolean input has a positive-Born execution
prefix with at least m/2 literal bit queries. The same program permits
unbounded time, changing finite workspaces, adaptive instruments, and
controlled/adjoint queries. The optional second oracle is input-independent. -/
theorem QuantumProgram.lemma66 {m : ℕ}
    (program : QuantumProgram (Physical.BitBasis m) B d Node) (out : Fin d)
    (Ub : Matrix.unitaryGroup B ℂ) (node : Node w) (psi : Fin w → ℂ)
    (hpsi : ‖WithLp.toLp 2 psi‖ = 1)
    (hcorrect : program.ComputesParity out Ub node psi) :
    ∃ (z : BitString m) (fuel : ℕ) (k : (program.unroll out fuel node).Terminal),
      0 < ((program.unroll out fuel node).terminalPath (.initial psi) k).bornWeight
        (Physical.standardBitOracle z) Ub ∧
      m ≤ 2 * ((program.unroll out fuel node).terminalPath (.initial psi) k).matrixQueries :=
  program.parity_hard_run_of_polynomial_oracle out (standardBitPolynomial m)
    (standardBitPolynomial_degree m) Physical.standardBitOracle Ub standardBitPolynomial_eval
    node psi hpsi hcorrect


end OptimalQLS.LowerBounds
