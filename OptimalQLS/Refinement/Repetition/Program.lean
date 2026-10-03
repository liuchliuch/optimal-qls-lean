import OptimalQLS.Refinement.Repetition.Measurement
import OptimalQLS.Repetition

/-! Finite repeat-until-success, with literal circuit instructions and an
oracle-independent, normalized coordinate measurement/reset between runs. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.Refinement.Repetition
open Matrix LowerBounds
set_option maxHeartbeats 20000
universe u v
variable {A : Type u} {B : Type v} {d w : ℕ}


def prepend (c : QueryCircuit A B (Fin w))
    (next : FiniteOracleProgram A B d w) : FiniteOracleProgram A B d w :=
  match c with
  | [] => next
  | .work U :: rest => .instrument 1 (fun _ => w) (fun _ => U.val)
      (by rw [Fin.sum_univ_one]; exact U.property.1) (fun _ => prepend rest next)
  | .matrixCall p adj :: rest => .matrixQuery p adj (prepend rest next)
  | .vectorCall p adj :: rest => .vectorQuery p adj (prepend rest next)


def failureOutput (out : Fin d) (w : ℕ) : FiniteOracleProgram A B d w :=
  .instrument w (fun _ => d) (abortBasisKraus out) (abortBasisKraus_normalized out)
    (fun _ => .output false false)


def repeatProgram (c : QueryCircuit A B (Fin w)) (e : Fin d ↪ Fin w)
    (zero : Fin w) (out : Fin d) : ℕ → FiniteOracleProgram A B d w
  | 0 => failureOutput out w
  | n + 1 => prepend c (.instrument (w + 1) (nextDimension d w)
      (measurementKraus e zero) (measurementKraus_complete e zero)
      (Fin.cases (.output true false) (fun _ => repeatProgram c e zero out n)))

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]


theorem prepend_executeDensity (c : QueryCircuit A B (Fin w))
    (next : FiniteOracleProgram A B d w) (UA : Matrix.unitaryGroup A ℂ)
    (Ub : Matrix.unitaryGroup B ℂ) (select : Bool → Bool) (v : Fin w → ℂ) :
    (prepend c next).executeDensity UA Ub select v =
      next.executeDensity UA Ub select ((c.eval UA Ub).val *ᵥ v) := by
  induction c generalizing v with
  | nil => simp [prepend, QueryCircuit.eval]
  | cons gate c ih =>
    cases gate <;>
      simp [prepend, FiniteOracleProgram.executeDensity, QueryCircuit.eval,
        QueryInstruction.eval, ih, ← Matrix.mulVec_mulVec]


theorem executeDensity_smul (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (select : Bool → Bool) (a : ℂ) (v : Fin w → ℂ) :
    tree.executeDensity UA Ub select (a • v) =
      Complex.normSq a • tree.executeDensity UA Ub select v := by
  induction tree with
  | output flag aborted =>
    simp only [FiniteOracleProgram.executeDensity]
    split <;> simp [pureDensity_complex_smul]
  | matrixQuery p adj next ih =>
    simpa only [FiniteOracleProgram.executeDensity, Matrix.mulVec_smul] using ih ((p.apply (if adj then UA⁻¹ else UA)).val *ᵥ v)
  | vectorQuery p adj next ih =>
    simpa only [FiniteOracleProgram.executeDensity, Matrix.mulVec_smul] using ih ((p.apply (if adj then Ub⁻¹ else Ub)).val *ᵥ v)
  | instrument r dims K hn next ih =>
    simp only [FiniteOracleProgram.executeDensity, Matrix.mulVec_smul, ih, Finset.smul_sum]


theorem failureOutput_executeDensity (out : Fin d) (UA : Matrix.unitaryGroup A ℂ)
    (Ub : Matrix.unitaryGroup B ℂ) (select : Bool → Bool) (v : Fin w → ℂ) :
    (failureOutput (A := A) (B := B) out w).executeDensity UA Ub select v =
      if select false then bornMass v • pureDensity (basis out) else 0 := by
  have hk (j : Fin w) : abortBasisKraus out j *ᵥ v = v j • basis out := by
    ext i
    simp [abortBasisKraus, Matrix.mulVec, dotProduct, basis]
  simp only [failureOutput, FiniteOracleProgram.executeDensity, hk, pureDensity_complex_smul]
  split <;> simp_all [bornMass, Finset.sum_smul]

def runState (c : QueryCircuit A B (Fin w)) (zero : Fin w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) : Fin w → ℂ :=
  (c.eval UA Ub).val *ᵥ basis zero

def successVector (c : QueryCircuit A B (Fin w)) (e : Fin d ↪ Fin w) (zero : Fin w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) : Fin d → ℂ :=
  fun i => runState c zero UA Ub (e i)

def successMass (c : QueryCircuit A B (Fin w)) (e : Fin d ↪ Fin w) (zero : Fin w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) : ℝ :=
  bornMass (successVector c e zero UA Ub)


theorem runState_bornMass (c : QueryCircuit A B (Fin w)) (zero : Fin w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    bornMass (runState c zero UA Ub) = 1 := by
  rw [runState, unitary_bornMass, basis_bornMass]



end OptimalQLS.Refinement.Repetition
