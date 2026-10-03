import OptimalQLS.Reduction.ProgramComposition

/-! At most three runs of the supplied normalized solver, with real extraction
and measured reset between attempts. Independence follows from these semantics. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.Reduction
open Matrix LowerBounds Refinement.Repetition
set_option maxHeartbeats 500000
universe u v
variable {A : Type u} {B : Type v} {d m w : ℕ}

def retrySolver (tree : FiniteOracleProgram A B m w) (e : Fin d ↪ Fin m)
    (zero : Fin w) (out : Fin d) : ℕ → FiniteOracleProgram A B d w
  | 0 => failureOutput out w
  | n+1 => extractAndRetry tree e zero out (retrySolver tree e zero out n)

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def attemptDensity (tree : FiniteOracleProgram A B m w) (e : Fin d ↪ Fin m)
    (zero : Fin w) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    Matrix (Fin d) (Fin d) ℂ := extractDensity e (tree.executeDensity UA Ub id (basis zero))

def attemptMass (tree : FiniteOracleProgram A B m w) (e : Fin d ↪ Fin m)
    (zero : Fin w) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) : ℝ :=
  (attemptDensity tree e zero UA Ub).trace.re

theorem retrySolver_step (tree : FiniteOracleProgram A B m w) (e : Fin d ↪ Fin m)
    (zero : Fin w) (out : Fin d) (n : ℕ)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (select : Bool → Bool) :
    (retrySolver tree e zero out (n+1)).executeDensity UA Ub select (basis zero) =
      (if select true then attemptDensity tree e zero UA Ub else 0) +
      (1-attemptMass tree e zero UA Ub) •
        (retrySolver tree e zero out n).executeDensity UA Ub select (basis zero) := by
  rw [retrySolver, extractAndRetry_density, basis_bornMass]
  rfl

theorem retrySolver_successDensity (tree : FiniteOracleProgram A B m w) (e : Fin d ↪ Fin m)
    (zero : Fin w) (out : Fin d) (n : ℕ)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (retrySolver tree e zero out n).executeDensity UA Ub id (basis zero) =
      geometricWeight (1-attemptMass tree e zero UA Ub) n • attemptDensity tree e zero UA Ub := by
  induction n with
  | zero => simp [retrySolver, failureOutput_executeDensity, geometricWeight]
  | succ n ih =>
    rw [retrySolver_step, ih, geometricWeight]
    simp [smul_smul, add_smul]

theorem retrySolver_successProbability (tree : FiniteOracleProgram A B m w) (e : Fin d ↪ Fin m)
    (zero : Fin w) (out : Fin d) (n : ℕ)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (retrySolver tree e zero out n).successProbability UA Ub (basis zero) =
      1-(1-attemptMass tree e zero UA Ub)^n := by
  rw [FiniteOracleProgram.successProbability, retrySolver_successDensity,
    Matrix.trace_smul, Complex.smul_re]
  exact geometricWeight_mul _ n

theorem attemptMass_bounds (tree : FiniteOracleProgram A B m w) (e : Fin d ↪ Fin m)
    (zero : Fin w) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    0 ≤ attemptMass tree e zero UA Ub ∧ attemptMass tree e zero UA Ub ≤ 1 := by
  have h := (retrySolver tree e zero out 1).successProbability_bounds UA Ub (basis zero) (basis_norm zero)
  rw [retrySolver_successProbability] at h
  simpa using h

theorem retrySolver_conditionalOutput (tree : FiniteOracleProgram A B m w) (e : Fin d ↪ Fin m)
    (zero : Fin w) (out : Fin d) (n : ℕ)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (hp : 0 < attemptMass tree e zero UA Ub) (hn : n ≠ 0) :
    (retrySolver tree e zero out n).conditionalOutput UA Ub (basis zero) =
      (attemptMass tree e zero UA Ub)⁻¹ • attemptDensity tree e zero UA Ub := by
  have hq := sub_nonneg.mpr (attemptMass_bounds tree e zero out UA Ub).2
  have hg := geometricWeight_pos hq hn
  have hprob : (retrySolver tree e zero out n).successProbability UA Ub (basis zero) =
      geometricWeight (1-attemptMass tree e zero UA Ub) n * attemptMass tree e zero UA Ub := by
    rw [retrySolver_successProbability, geometricWeight_mul]
  rw [FiniteOracleProgram.conditionalOutput, hprob, retrySolver_successDensity, smul_smul]
  congr 1
  field_simp

/-- The success bound is derived from the executed quantum program. No
independent-attempt hypothesis appears in the statement. -/
theorem three_attempts_success (tree : FiniteOracleProgram A B m w) (e : Fin d ↪ Fin m)
    (zero : Fin w) (out : Fin d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (hp : 3/8 ≤ attemptMass tree e zero UA Ub) :
    (2 : ℝ)/3 < (retrySolver tree e zero out 3).successProbability UA Ub (basis zero) := by
  rw [retrySolver_successProbability]
  have hb := attemptMass_bounds tree e zero out UA Ub
  have hpow := pow_le_pow_left₀ (sub_nonneg.mpr hb.2)
    (show 1-attemptMass tree e zero UA Ub ≤ (5:ℝ)/8 by linarith) 3
  norm_num at hpow ⊢
  linarith

theorem attemptDensity_of_pure_output (tree : FiniteOracleProgram A B m w)
    (e : Fin d ↪ Fin m) (zero : Fin w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (y : Fin m → ℂ) (hp : 0 < tree.successProbability UA Ub (basis zero))
    (hy : tree.conditionalOutput UA Ub (basis zero) = pureDensity y) :
    attemptDensity tree e zero UA Ub =
      tree.successProbability UA Ub (basis zero) • pureDensity (fun i => y (e i)) := by
  rw [attemptDensity, tree.successDensity_eq_probability_smul UA Ub (basis zero) hp,
    hy, map_smul, extractDensity_pure]

theorem attemptMass_of_pure_output (tree : FiniteOracleProgram A B m w)
    (e : Fin d ↪ Fin m) (zero : Fin w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (y : Fin m → ℂ) (hp : 0 < tree.successProbability UA Ub (basis zero))
    (hy : tree.conditionalOutput UA Ub (basis zero) = pureDensity y) :
    attemptMass tree e zero UA Ub =
      tree.successProbability UA Ub (basis zero) * bornMass (fun i => y (e i)) := by
  rw [attemptMass, attemptDensity_of_pure_output tree e zero UA Ub y hp hy,
    Matrix.trace_smul, Complex.smul_re, ← bornMass_eq_trace]
  rfl

theorem normalized_density (v : Fin d → ℂ) :
    pureDensity (fun i => (NormedSpace.normalize (WithLp.toLp 2 v) : EuclideanSpace ℂ (Fin d)) i) =
      (bornMass v)⁻¹ • pureDensity v := by
  have he : (fun i => (NormedSpace.normalize (WithLp.toLp 2 v) : EuclideanSpace ℂ (Fin d)) i) =
      (‖WithLp.toLp 2 v‖⁻¹ : ℂ) • v := by
    ext i
    simp [NormedSpace.normalize, Complex.real_smul]
  rw [he, pureDensity_complex_smul, bornMass_eq_norm_sq]
  congr 1
  simp [Complex.normSq_inv, Complex.normSq_ofReal, pow_two]

theorem retrySolver_pure_output (tree : FiniteOracleProgram A B m w)
    (e : Fin d ↪ Fin m) (zero : Fin w) (out : Fin d) (n : ℕ)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (y : Fin m → ℂ) (hp : 0 < tree.successProbability UA Ub (basis zero))
    (hy : tree.conditionalOutput UA Ub (basis zero) = pureDensity y)
    (he : 0 < bornMass (fun i => y (e i))) (hn : n ≠ 0) :
    (retrySolver tree e zero out n).conditionalOutput UA Ub (basis zero) =
      pureDensity (fun i => (NormedSpace.normalize
        (WithLp.toLp 2 (fun i => y (e i))) : EuclideanSpace ℂ (Fin d)) i) := by
  have hmass := attemptMass_of_pure_output tree e zero UA Ub y hp hy
  have hpos : 0 < attemptMass tree e zero UA Ub := by rw [hmass]; positivity
  rw [retrySolver_conditionalOutput tree e zero out n UA Ub hpos hn,
    hmass, attemptDensity_of_pure_output tree e zero UA Ub y hp hy,
    normalized_density, smul_smul]
  congr 1
  field_simp

end OptimalQLS.Reduction
