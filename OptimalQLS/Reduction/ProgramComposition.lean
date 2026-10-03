import OptimalQLS.Refinement.Repetition.Complete
import OptimalQLS.Reduction.Extraction

/-! Actual finite-program continuation, data extraction, and measured reset. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.Reduction
open Matrix LowerBounds Refinement.Repetition
set_option maxHeartbeats 500000
universe u v
variable {A : Type u} {B : Type v} {d m w : ℕ}

def bindOutput : {w : ℕ} → FiniteOracleProgram A B m w →
    (Bool → FiniteOracleProgram A B d m) → FiniteOracleProgram A B d w
  | _, .output flag _, next => next flag
  | _, .matrixQuery p adj rest, next => .matrixQuery p adj (bindOutput rest next)
  | _, .vectorQuery p adj rest, next => .vectorQuery p adj (bindOutput rest next)
  | _, .instrument r dims K hn rest, next =>
    .instrument r dims K hn (fun i => bindOutput (rest i) next)

def measuredReset (zero : Fin w) (next : FiniteOracleProgram A B d w) :
    FiniteOracleProgram A B d m :=
  .instrument m (fun _ => w) (abortBasisKraus zero)
    (abortBasisKraus_normalized zero) (fun _ => next)

def measureExtract (e : Fin d ↪ Fin m) (zero : Fin w) (out : Fin d)
    (next : FiniteOracleProgram A B d w) : FiniteOracleProgram A B d m :=
  .instrument (m+1) (nextDimension d m) (measurementKraus e (e out))
    (measurementKraus_complete e (e out))
    (Fin.cases (.output true false) (fun _ => measuredReset zero next))

def extractAndRetry (tree : FiniteOracleProgram A B m w)
    (e : Fin d ↪ Fin m) (zero : Fin w) (out : Fin d)
    (next : FiniteOracleProgram A B d w) : FiniteOracleProgram A B d w :=
  bindOutput tree (fun flag => if flag then measureExtract e zero out next
    else measuredReset zero next)

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

theorem bindOutput_density (tree : FiniteOracleProgram A B m w)
    (next : Bool → FiniteOracleProgram A B d m)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (select : Bool → Bool)
    (L : Bool → Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ)
    (hL : ∀ flag x, (next flag).executeDensity UA Ub select x = L flag (pureDensity x))
    (x : Fin w → ℂ) :
    (bindOutput tree next).executeDensity UA Ub select x =
      L true (tree.executeDensity UA Ub id x) +
      L false (tree.executeDensity UA Ub Bool.not x) := by
  induction tree with
  | output flag aborted => cases flag <;> simp [bindOutput, FiniteOracleProgram.executeDensity, hL]
  | matrixQuery p adj tree ih => exact ih _
  | vectorQuery p adj tree ih => exact ih _
  | instrument r dims K hn tree ih =>
    simp only [bindOutput, FiniteOracleProgram.executeDensity, ih, map_sum, Finset.sum_add_distrib]

theorem measuredReset_density (zero : Fin w) (next : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (select : Bool → Bool) (x : Fin m → ℂ) :
    (measuredReset zero next).executeDensity UA Ub select x =
      bornMass x • next.executeDensity UA Ub select (basis zero) := by
  have hk (j : Fin m) : abortBasisKraus zero j *ᵥ x = x j • basis zero := by
    ext i
    simp [abortBasisKraus, Matrix.mulVec, dotProduct, basis]
  simp only [measuredReset, FiniteOracleProgram.executeDensity, hk, executeDensity_smul,
    ← Finset.sum_smul]
  rfl

theorem measureExtract_density (e : Fin d ↪ Fin m) (zero : Fin w) (out : Fin d)
    (next : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (select : Bool → Bool) (x : Fin m → ℂ) :
    (measureExtract e zero out next).executeDensity UA Ub select x =
      (if select true then pureDensity (fun i => x (e i)) else 0) +
      (bornMass x - bornMass (fun i => x (e i))) •
        next.executeDensity UA Ub select (basis zero) := by
  simp only [measureExtract, FiniteOracleProgram.executeDensity, Fin.sum_univ_succ]
  change (if select true then pureDensity (acceptMatrix e *ᵥ x) else 0) +
    (∑ j, (measuredReset zero next).executeDensity UA Ub select (resetMatrix e (e out) j *ᵥ x)) = _
  simp only [acceptMatrix_mulVec, measuredReset_density, resetMatrix_mulVec,
    bornMass_smul, basis_bornMass, mul_one, ← Finset.sum_smul]
  rw [rejection_mass e (e out)]

/-- Compression by the actual accepted Kraus operator, as a real linear map. -/
def extractDensity (e : Fin d ↪ Fin m) :
    Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ where
  toFun X := acceptMatrix e * X * (acceptMatrix e).conjTranspose
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' a X := by simp

theorem extractDensity_pure (e : Fin d ↪ Fin m) (x : Fin m → ℂ) :
    extractDensity e (pureDensity x) = pureDensity (fun i => x (e i)) := by
  change acceptMatrix e * pureDensity x * (acceptMatrix e).conjTranspose = _
  rw [← pureDensity_mulVec, acceptMatrix_mulVec]

def traceReal : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] ℝ where
  toFun X := X.trace.re
  map_add' X Y := by simp
  map_smul' a X := by simp

def resetDensity (R : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ :=
  (traceReal (m := m)).smulRight R

def acceptedContinuationDensity (e : Fin d ↪ Fin m) (select : Bool → Bool)
    (R : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ :=
  (if select true then extractDensity e else 0) +
    (traceReal - traceReal.comp (extractDensity e)).smulRight R

theorem program_total_trace (tree : FiniteOracleProgram A B m w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (x : Fin w → ℂ) :
    (tree.executeDensity UA Ub id x).trace.re +
      (tree.executeDensity UA Ub Bool.not x).trace.re = bornMass x := by
  have h := congrArg (fun X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ => X.trace.re)
    (tree.outputChannel_pureDensity UA Ub x)
  dsimp only at h
  rw [FiniteChannel.trace_apply, pureDensity_trace, LowerBounds.trace_blockDiagonal] at h
  simpa only [Complex.add_re, Complex.ofReal_re, bornMass_eq_norm_sq] using h.symm

theorem extractAndRetry_density (tree : FiniteOracleProgram A B m w)
    (e : Fin d ↪ Fin m) (zero : Fin w) (out : Fin d)
    (next : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (select : Bool → Bool) (x : Fin w → ℂ) :
    (extractAndRetry tree e zero out next).executeDensity UA Ub select x =
      (if select true then extractDensity e (tree.executeDensity UA Ub id x) else 0) +
      (bornMass x - (extractDensity e (tree.executeDensity UA Ub id x)).trace.re) •
        next.executeDensity UA Ub select (basis zero) := by
  let R := next.executeDensity UA Ub select (basis zero)
  let L := fun flag : Bool => if flag then acceptedContinuationDensity e select R else resetDensity R
  have hL : ∀ flag v, ((fun flag : Bool => if flag then measureExtract e zero out next
      else measuredReset zero next) flag).executeDensity UA Ub select v = L flag (pureDensity v) := by
    intro flag v
    cases flag <;> cases hs : select true <;> simp [L, R, measuredReset_density, measureExtract_density,
      resetDensity, acceptedContinuationDensity, extractDensity_pure, traceReal,
      ← bornMass_eq_trace, hs]
  rw [extractAndRetry, bindOutput_density _ _ UA Ub select L hL]
  have ht := program_total_trace tree UA Ub x
  simp only [L, Bool.true_eq, ite_true, Bool.false_eq_true, ite_false,
    acceptedContinuationDensity, resetDensity, LinearMap.add_apply,
    LinearMap.smulRight_apply, LinearMap.sub_apply, LinearMap.comp_apply]
  simp only [traceReal, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs
  · rw [add_assoc, ← add_smul]
    congr 1
    congr 1
    linarith
  · simp only [LinearMap.zero_apply, zero_add]
    rw [← add_smul]
    congr 1
    linarith

end OptimalQLS.Reduction
