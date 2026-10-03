import OptimalQLS.Refinement.Repetition.Program

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.Refinement.Repetition
open Matrix LowerBounds
set_option maxHeartbeats 100000
universe u v
variable {A : Type u} {B : Type v} {d w : ℕ}
variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

theorem repeatProgram_step (c : QueryCircuit A B (Fin w)) (e : Fin d ↪ Fin w)
    (zero : Fin w) (out : Fin d) (n : ℕ) (UA : Matrix.unitaryGroup A ℂ)
    (Ub : Matrix.unitaryGroup B ℂ) (select : Bool → Bool) :
    (repeatProgram c e zero out (n + 1)).executeDensity UA Ub select (basis zero) =
      (if select true then pureDensity (successVector c e zero UA Ub) else 0) +
      (1 - successMass c e zero UA Ub) •
        (repeatProgram c e zero out n).executeDensity UA Ub select (basis zero) := by
  rw [repeatProgram, prepend_executeDensity]
  simp only [FiniteOracleProgram.executeDensity, Fin.sum_univ_succ]
  change (if select true then pureDensity (acceptMatrix e *ᵥ runState c zero UA Ub) else 0) +
    (∑ j, (repeatProgram c e zero out n).executeDensity UA Ub select
      (resetMatrix e zero j *ᵥ runState c zero UA Ub)) = _
  simp only [acceptMatrix_mulVec, resetMatrix_mulVec, executeDensity_smul, ← Finset.sum_smul]
  rw [rejection_mass e zero, runState_bornMass]
  rfl

def geometricWeight (q : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => 1 + q * geometricWeight q n


theorem repeatProgram_successDensity (c : QueryCircuit A B (Fin w)) (e : Fin d ↪ Fin w)
    (zero : Fin w) (out : Fin d) (n : ℕ) (UA : Matrix.unitaryGroup A ℂ)
    (Ub : Matrix.unitaryGroup B ℂ) :
    (repeatProgram c e zero out n).executeDensity UA Ub id (basis zero) =
      geometricWeight (1 - successMass c e zero UA Ub) n •
        pureDensity (successVector c e zero UA Ub) := by
  induction n with
  | zero => simp [repeatProgram, failureOutput_executeDensity, geometricWeight]
  | succ n ih =>
    rw [repeatProgram_step, ih, geometricWeight]
    simp only [id_eq, Bool.true_eq, ite_true, smul_smul, add_smul, one_smul]


theorem repeatProgram_failureDensity (c : QueryCircuit A B (Fin w)) (e : Fin d ↪ Fin w)
    (zero : Fin w) (out : Fin d) (n : ℕ) (UA : Matrix.unitaryGroup A ℂ)
    (Ub : Matrix.unitaryGroup B ℂ) :
    (repeatProgram c e zero out n).executeDensity UA Ub Bool.not (basis zero) =
      (1 - successMass c e zero UA Ub) ^ n • pureDensity (basis out) := by
  induction n with
  | zero => simp [repeatProgram, failureOutput_executeDensity, basis_bornMass]
  | succ n ih =>
    rw [repeatProgram_step, ih]
    simp [pow_succ, smul_smul, mul_comm]


theorem geometricWeight_mul (p : ℝ) (n : ℕ) :
    geometricWeight (1 - p) n * p = 1 - (1 - p) ^ n := by
  induction n with
  | zero => simp [geometricWeight]
  | succ n ih => rw [geometricWeight, add_mul, mul_assoc, ih, pow_succ]; ring


theorem repeatProgram_successProbability (c : QueryCircuit A B (Fin w)) (e : Fin d ↪ Fin w)
    (zero : Fin w) (out : Fin d) (n : ℕ) (UA : Matrix.unitaryGroup A ℂ)
    (Ub : Matrix.unitaryGroup B ℂ) :
    (repeatProgram c e zero out n).successProbability UA Ub (basis zero) =
      1 - (1 - successMass c e zero UA Ub) ^ n := by
  rw [FiniteOracleProgram.successProbability, repeatProgram_successDensity,
    Matrix.trace_smul, Complex.smul_re]
  change geometricWeight (1 - successMass c e zero UA Ub) n *
    (pureDensity (successVector c e zero UA Ub)).trace.re = _
  rw [← bornMass_eq_trace]
  exact geometricWeight_mul _ n


theorem repeatProgram_failureProbability (c : QueryCircuit A B (Fin w)) (e : Fin d ↪ Fin w)
    (zero : Fin w) (out : Fin d) (n : ℕ) (UA : Matrix.unitaryGroup A ℂ)
    (Ub : Matrix.unitaryGroup B ℂ) :
    ((repeatProgram c e zero out n).executeDensity UA Ub Bool.not (basis zero)).trace.re =
      (1 - successMass c e zero UA Ub) ^ n := by
  rw [repeatProgram_failureDensity, Matrix.trace_smul, Complex.smul_re,
    ← bornMass_eq_trace, basis_bornMass, smul_eq_mul, mul_one]


theorem successMass_bounds (c : QueryCircuit A B (Fin w)) (e : Fin d ↪ Fin w)
    (zero : Fin w) (out : Fin d) (UA : Matrix.unitaryGroup A ℂ)
    (Ub : Matrix.unitaryGroup B ℂ) :
    0 ≤ successMass c e zero UA Ub ∧ successMass c e zero UA Ub ≤ 1 := by
  have h := (repeatProgram c e zero out 1).successProbability_bounds UA Ub (basis zero) (basis_norm zero)
  rw [repeatProgram_successProbability] at h
  simpa using h


theorem geometricWeight_nonneg {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    0 ≤ geometricWeight q n := by
  induction n with
  | zero => simp [geometricWeight]
  | succ n ih => exact add_nonneg (by norm_num) (mul_nonneg hq ih)

theorem geometricWeight_pos {q : ℝ} (hq : 0 ≤ q) {n : ℕ} (hn : n ≠ 0) :
    0 < geometricWeight q n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact add_pos_of_pos_of_nonneg (by norm_num) (mul_nonneg hq (geometricWeight_nonneg hq k))

theorem repeatProgram_conditionalOutput (c : QueryCircuit A B (Fin w)) (e : Fin d ↪ Fin w)
    (zero : Fin w) (out : Fin d) (n : ℕ) (UA : Matrix.unitaryGroup A ℂ)
    (Ub : Matrix.unitaryGroup B ℂ) (hp : 0 < successMass c e zero UA Ub) (hn : n ≠ 0) :
    (repeatProgram c e zero out n).conditionalOutput UA Ub (basis zero) =
      (successMass c e zero UA Ub)⁻¹ • pureDensity (successVector c e zero UA Ub) := by
  have hq := sub_nonneg.mpr (successMass_bounds c e zero out UA Ub).2
  have hg := geometricWeight_pos hq hn
  have hprob : (repeatProgram c e zero out n).successProbability UA Ub (basis zero) =
      geometricWeight (1 - successMass c e zero UA Ub) n * successMass c e zero UA Ub := by
    rw [repeatProgram_successProbability, geometricWeight_mul]
  rw [FiniteOracleProgram.conditionalOutput, hprob, repeatProgram_successDensity, smul_smul]
  congr 1
  field_simp

def normalizedSuccessVector (c : QueryCircuit A B (Fin w)) (e : Fin d ↪ Fin w) (zero : Fin w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) : Fin d → ℂ :=
  ((Real.sqrt (successMass c e zero UA Ub) : ℂ)⁻¹) • successVector c e zero UA Ub

theorem repeatProgram_conditionalOutput_pure (c : QueryCircuit A B (Fin w)) (e : Fin d ↪ Fin w)
    (zero : Fin w) (out : Fin d) (n : ℕ) (UA : Matrix.unitaryGroup A ℂ)
    (Ub : Matrix.unitaryGroup B ℂ) (hp : 0 < successMass c e zero UA Ub) (hn : n ≠ 0) :
    (repeatProgram c e zero out n).conditionalOutput UA Ub (basis zero) =
      pureDensity (normalizedSuccessVector c e zero UA Ub) := by
  rw [repeatProgram_conditionalOutput c e zero out n UA Ub hp hn,
    normalizedSuccessVector, pureDensity_complex_smul]
  congr 1
  simp only [Complex.normSq_inv, Complex.normSq_ofReal]
  rw [← pow_two, Real.sq_sqrt hp.le]

theorem normalizedSuccessVector_norm (c : QueryCircuit A B (Fin w)) (e : Fin d ↪ Fin w)
    (zero : Fin w) (UA : Matrix.unitaryGroup A ℂ)
    (Ub : Matrix.unitaryGroup B ℂ) (hp : 0 < successMass c e zero UA Ub) :
    ‖WithLp.toLp 2 (normalizedSuccessVector c e zero UA Ub)‖ = 1 := by
  have h : bornMass (normalizedSuccessVector c e zero UA Ub) = 1 := by
    rw [normalizedSuccessVector, bornMass_smul]
    change Complex.normSq ((Real.sqrt (successMass c e zero UA Ub) : ℂ)⁻¹) *
      successMass c e zero UA Ub = 1
    simp only [Complex.normSq_inv, Complex.normSq_ofReal]
    rw [← pow_two, Real.sq_sqrt hp.le, inv_mul_cancel₀ hp.ne']
  rw [bornMass_eq_norm_sq] at h
  nlinarith [norm_nonneg (WithLp.toLp 2 (normalizedSuccessVector c e zero UA Ub))]

end OptimalQLS.Refinement.Repetition
