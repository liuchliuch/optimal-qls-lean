import OptimalQLS.LowerBounds.QuantumProgram
import OptimalQLS.LowerBounds.FinitePrefixApproximation

/-!
# Monotone completed densities of an unbounded typed quantum program

Fuel aborts are omitted from the completed block. More fuel adds a positive
semidefinite contribution. The completed trace is bounded by the literal
initial Born mass, independently of termination or workspace growth.
-/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
namespace OptimalQLS.LowerBounds
open Matrix Filter QuantumChannelStein.TraceNorm
universe u v r
variable {A : Type u} {B : Type v} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  {d w : ℕ} {Node : ℕ → Type r}

def FiniteOracleProgram.completedDensity (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    {w : ℕ} → FiniteOracleProgram A B d w → (Fin w → ℂ) → Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ
  | _, .output success aborted, psi => if aborted then 0 else
      flagInjection success * pureDensity psi * (flagInjection success).conjTranspose
  | w, .matrixQuery port adj next, psi => next.completedDensity UA Ub
      ((port.apply (if adj then UA⁻¹ else UA) : Matrix (Fin w) (Fin w) ℂ) *ᵥ psi)
  | w, .vectorQuery port adj next, psi => next.completedDensity UA Ub
      ((port.apply (if adj then Ub⁻¹ else Ub) : Matrix (Fin w) (Fin w) ℂ) *ᵥ psi)
  | _, .instrument _ _ K _ next, psi => ∑ i, (next i).completedDensity UA Ub (K i *ᵥ psi)

theorem FiniteOracleProgram.completedDensity_positive (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) :
    (tree.completedDensity UA Ub psi).PosSemidef := by
  induction tree with
  | output success aborted =>
    unfold completedDensity
    split
    · exact Matrix.PosSemidef.zero
    · exact (pureDensity_positive psi).mul_mul_conjTranspose_same _
  | matrixQuery port adj next ih => exact ih _
  | vectorQuery port adj next ih => exact ih _
  | instrument rank dims K hn next ih =>
    exact Finset.sum_induction _ _ (fun _ _ hX hY => hX.add hY) Matrix.PosSemidef.zero (fun i _ => ih i _)

theorem FiniteOracleProgram.completedDensity_trace_le (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) :
    (tree.completedDensity UA Ub psi).trace.re ≤ bornMass psi := by
  induction tree with
  | output success aborted =>
    unfold completedDensity
    split
    · simp only [Matrix.trace_zero, Complex.zero_re]
      exact Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)
    · rw [Matrix.trace_mul_cycle, flagInjection_gram, Matrix.one_mul, bornMass_eq_trace]
  | matrixQuery port adj next ih =>
    exact (ih _).trans_eq (unitary_bornMass _ psi)
  | vectorQuery port adj next ih =>
    exact (ih _).trans_eq (unitary_bornMass _ psi)
  | instrument rank dims K hn next ih =>
    change (∑ i, (next i).completedDensity UA Ub (K i *ᵥ psi)).trace.re ≤ _
    rw [Matrix.trace_sum, Complex.re_sum, ← varying_instrument_bornMass dims K hn psi]
    exact Finset.sum_le_sum (fun i _ => ih i _)

@[simp] theorem FiniteOracleProgram.abortProgram_completedDensity (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) :
    (FiniteOracleProgram.abortProgram out w).completedDensity UA Ub psi = 0 := by
  simp [abortProgram, completedDensity]

def QuantumProgram.completedPrefix (program : QuantumProgram A B d Node) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (node : Node w) (psi : Fin w → ℂ) (fuel : ℕ) :
    Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ := (program.unroll out fuel node).completedDensity UA Ub psi

theorem QuantumProgram.completedPrefix_succ_positive (program : QuantumProgram A B d Node) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (node : Node w) (psi : Fin w → ℂ) (fuel : ℕ) :
    (program.completedPrefix out UA Ub node psi (fuel + 1) - program.completedPrefix out UA Ub node psi fuel).PosSemidef := by
  induction fuel generalizing w with
  | zero =>
    simp only [completedPrefix, unroll, FiniteOracleProgram.abortProgram_completedDensity, sub_zero]
    exact FiniteOracleProgram.completedDensity_positive _ UA Ub psi
  | succ fuel ih =>
    unfold completedPrefix
    simp only [unroll]
    cases program.step node with
    | output success =>
      simp only [FiniteOracleProgram.completedDensity, Bool.false_eq_true, if_false, sub_self]
      exact Matrix.PosSemidef.zero
    | matrixQuery port adj next => exact ih next _
    | vectorQuery port adj next => exact ih next _
    | instrument rank dims K hn next =>
      simp only [FiniteOracleProgram.completedDensity, ← Finset.sum_sub_distrib]
      exact Finset.sum_induction _ _ (fun _ _ hX hY => hX.add hY) Matrix.PosSemidef.zero (fun i _ => ih (next i) _)

theorem QuantumProgram.completedPrefix_increment_positive (program : QuantumProgram A B d Node) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (node : Node w) (psi : Fin w → ℂ)
    {n m : ℕ} (hnm : n ≤ m) :
    (program.completedPrefix out UA Ub node psi m - program.completedPrefix out UA Ub node psi n).PosSemidef := by
  induction hnm with
  | refl => simp only [sub_self]; exact Matrix.PosSemidef.zero
  | @step m hm ih =>
    have hstep := program.completedPrefix_succ_positive out UA Ub node psi m
    have heq : program.completedPrefix out UA Ub node psi (m + 1) - program.completedPrefix out UA Ub node psi n =
      (program.completedPrefix out UA Ub node psi (m + 1) - program.completedPrefix out UA Ub node psi m) +
      (program.completedPrefix out UA Ub node psi m - program.completedPrefix out UA Ub node psi n) := by abel
    rw [heq]
    exact hstep.add ih

theorem QuantumProgram.completedPrefix_cauchy (program : QuantumProgram A B d Node) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (node : Node w) (psi : Fin w → ℂ) :
    CauchySeq (program.completedPrefix out UA Ub node psi) := by
  let f : ℕ → ℝ := fun n => (program.completedPrefix out UA Ub node psi n).trace.re
  have hmono : Monotone f := by
    intro n m hnm
    have h := (program.completedPrefix_increment_positive out UA Ub node psi hnm).trace_nonneg.1
    simpa [f, Matrix.trace_sub] using h
  have hbdd : BddAbove (Set.range f) := by
    refine ⟨bornMass psi, ?_⟩
    rintro x ⟨n, rfl⟩
    exact (program.unroll out n node).completedDensity_trace_le UA Ub psi
  let L := ⨆ n, f n
  have hlim : Tendsto f atTop (𝓝 L) := tendsto_atTop_ciSup hmono hbdd
  apply cauchySeq_of_le_tendsto_0' (fun n => L - f n)
  · intro n m hnm
    rw [dist_eq_norm, norm_sub_rev]
    apply (opNorm_le_traceNorm _).trans
    rw [traceNorm_positive_eq_trace _ (program.completedPrefix_increment_positive out UA Ub node psi hnm),
      Matrix.trace_sub, Complex.sub_re]
    exact sub_le_sub_right (le_ciSup hbdd m) _
  · simpa using (tendsto_const_nhds (x := L)).sub hlim

def QuantumProgram.completedLimit (program : QuantumProgram A B d Node) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (node : Node w) (psi : Fin w → ℂ) :
    Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ :=
  Classical.choose (cauchySeq_tendsto_of_complete (program.completedPrefix_cauchy out UA Ub node psi))

theorem QuantumProgram.completedLimit_tendsto (program : QuantumProgram A B d Node) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (node : Node w) (psi : Fin w → ℂ) :
    Tendsto (program.completedPrefix out UA Ub node psi) atTop (𝓝 (program.completedLimit out UA Ub node psi)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (program.completedPrefix_cauchy out UA Ub node psi))

end OptimalQLS.LowerBounds
