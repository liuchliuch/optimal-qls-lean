import OptimalQLS.LowerBounds.ProgramFailureCompletion
import OptimalQLS.LowerBounds.OrdinaryProgramOneSided

/-!
# Actual total output of an unbounded varying-workspace instruction program

Completed output has a proved norm limit. Every unfinished branch is completed
into one fixed failure state, so no termination premise is introduced. The
same program's literal finite prefixes define its worst-case query bounds.
-/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
namespace OptimalQLS.LowerBounds
open Matrix Filter
universe u v r
variable {A : Type u} {B : Type v} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  {d w : ℕ} {Node : ℕ → Type r}

def QuantumProgram.totalOutput (program : QuantumProgram A B d Node) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (node : Node w) (psi : Fin w → ℂ) :
    Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ :=
  program.completedLimit out UA Ub node psi +
    (bornMass psi - (program.completedLimit out UA Ub node psi).trace.re) • ordinaryFailureState out

theorem QuantumProgram.totalOutput_tendsto (program : QuantumProgram A B d Node) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (node : Node w) (psi : Fin w → ℂ) :
    Tendsto (fun n => (program.unroll out n node).ordinaryOutput UA Ub psi) atTop
      (𝓝 (program.totalOutput out UA Ub node psi)) := by
  have hc := program.completedLimit_tendsto out UA Ub node psi
  have ht := (Complex.continuous_re.comp matrixTrace_continuous).tendsto (program.completedLimit out UA Ub node psi)
  have hr := (tendsto_const_nhds (x := bornMass psi)).sub (ht.comp hc)
  have h := hc.add (hr.smul_const (ordinaryFailureState out))
  convert h using 1
  funext n
  exact program.unroll_output_decomposition out UA Ub n node psi

theorem QuantumProgram.totalOutput_positive (program : QuantumProgram A B d Node) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (node : Node w) (psi : Fin w → ℂ) :
    (program.totalOutput out UA Ub node psi).PosSemidef := by
  apply matrixPosSemidef_isClosed.mem_of_tendsto (program.totalOutput_tendsto out UA Ub node psi)
  exact Filter.Eventually.of_forall (fun n => (program.unroll out n node).ordinaryOutput_positive UA Ub psi)

theorem QuantumProgram.totalOutput_trace (program : QuantumProgram A B d Node) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (node : Node w) (psi : Fin w → ℂ) :
    (program.totalOutput out UA Ub node psi).trace = (bornMass psi : ℂ) := by
  have hlim := (matrixTrace_continuous.tendsto _).comp (program.totalOutput_tendsto out UA Ub node psi)
  have heq : (fun n => ((program.unroll out n node).ordinaryOutput UA Ub psi).trace) = fun _ : ℕ => (bornMass psi : ℂ) := by
    funext n
    rw [FiniteOracleProgram.ordinaryOutput, FiniteChannel.trace_apply, pureDensity_trace, bornMass_eq_norm_sq]
  change Tendsto (fun n => ((program.unroll out n node).ordinaryOutput UA Ub psi).trace) atTop _ at hlim
  rw [heq] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- A pointwise worst-case resource bound is a bound on every positive Born
run of every actual finite execution prefix, including nonterminating runs. -/
def QuantumProgram.PointwiseVectorBound (program : QuantumProgram A B d Node) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (node : Node w) (psi : Fin w → ℂ) (q : ℕ) : Prop :=
  ∀ fuel, (program.unroll out fuel node).PointwiseVectorBound UA Ub psi q

/-- The one-sided hybrid now holds for the actual unbounded instruction
coalgebra with arbitrary finite workspace at each step. No independent model
correspondence or almost-sure-halting hypothesis occurs. -/
theorem QuantumProgram.one_sided_vector_hybrid (program : QuantumProgram A B d Node) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (U V : Matrix.unitaryGroup B ℂ) (node : Node w) (psi : Fin w → ℂ)
    (hpsi : ‖WithLp.toLp 2 psi‖ = 1) (q : ℕ) (hq : program.PointwiseVectorBound out UA U node psi q) :
    traceDistance (program.totalOutput out UA U node psi) (program.totalOutput out UA V node psi) ≤
      3 * (q : ℝ) * ‖(U : Matrix B B ℂ) - (V : Matrix B B ℂ)‖ := by
  have hlim := traceDistance_continuous.tendsto
    (program.totalOutput out UA U node psi, program.totalOutput out UA V node psi)
  have hout := (program.totalOutput_tendsto out UA U node psi).prodMk_nhds (program.totalOutput_tendsto out UA V node psi)
  have hbound (fuel : ℕ) :
      traceDistance ((program.unroll out fuel node).ordinaryOutput UA U psi)
        ((program.unroll out fuel node).ordinaryOutput UA V psi) ≤ 3 * (q : ℝ) * ‖(U : Matrix B B ℂ) - (V : Matrix B B ℂ)‖ := by
    let tree := program.unroll out fuel node
    have h := tree.eraseAbort.ordinary_one_sided_vector_hybrid tree.eraseAbort_clean out q UA U V psi hpsi
      (tree.eraseAbort_pointwiseVectorBound UA U psi q (hq fuel))
    simpa only [FiniteOracleProgram.ordinaryOutput, tree.eraseAbort_outputChannel] using h
  exact le_of_tendsto (hlim.comp hout) (Filter.Eventually.of_forall hbound)

/-- Every finite family of oracle pairs has a common approximating prefix. -/
theorem QuantumProgram.exists_common_prefix {I : Type*} [Finite I]
    (program : QuantumProgram A B d Node) (out : Fin d)
    (UA : I → Matrix.unitaryGroup A ℂ) (Ub : I → Matrix.unitaryGroup B ℂ)
    (node : Node w) (psi : Fin w → ℂ) {eta : ℝ} (heta : 0 < eta) :
    ∃ cutoff : ℕ, ∀ i, ∀ n ≥ cutoff,
      traceDistance ((program.unroll out n node).ordinaryOutput (UA i) (Ub i) psi)
        (program.totalOutput out (UA i) (Ub i) node psi) < eta := by
  have hi (i : I) : ∀ᶠ n in atTop,
      traceDistance ((program.unroll out n node).ordinaryOutput (UA i) (Ub i) psi)
        (program.totalOutput out (UA i) (Ub i) node psi) < eta := by
    have h := traceDistance_continuous.tendsto
      (program.totalOutput out (UA i) (Ub i) node psi, program.totalOutput out (UA i) (Ub i) node psi)
    have hx := (program.totalOutput_tendsto out (UA i) (Ub i) node psi).prodMk_nhds
      (tendsto_const_nhds (x := program.totalOutput out (UA i) (Ub i) node psi))
    have hz : Tendsto (fun n => traceDistance ((program.unroll out n node).ordinaryOutput (UA i) (Ub i) psi)
        (program.totalOutput out (UA i) (Ub i) node psi)) atTop (𝓝 0) := by simpa using h.comp hx
    exact hz.eventually (gt_mem_nhds heta)
  have hall := eventually_all.mpr hi
  obtain ⟨cutoff, hcutoff⟩ := eventually_atTop.mp hall
  exact ⟨cutoff, fun i n hn => hcutoff n hn i⟩

end OptimalQLS.LowerBounds
