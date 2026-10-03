import OptimalQLS.OracleCircuit
import Mathlib.Analysis.Complex.Circle
import Mathlib.Tactic

/-!
# Concrete alternating phase/query words

This file constructs the actual unitary instruction list used in singular
value transformation and verifies its separate oracle query counts. It
makes no assertion that a bounded polynomial has the required phase list;
that phase-factorization theorem is proved in QSPFactorization and BoundedQSP.
`workInstructions` counts arbitrary diagonal work instructions, not a
synthesis into elementary one- and two-qubit gates.
-/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Matrix
open scoped ComplexConjugate

variable {A B W : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype W] [DecidableEq W]

/-- An explicit oracle-independent diagonal unitary. -/
def diagonalPhase (φ : W → Circle) : Matrix.unitaryGroup W ℂ :=
  ⟨Matrix.diagonal (fun w => (φ w : ℂ)), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    have heq : (fun w => (φ w : ℂ) * star (φ w : ℂ)) = (1 : W → ℂ) := by
      funext w
      change (φ w : ℂ) * star (φ w : ℂ) = 1
      simp only [RCLike.star_def, Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]
    change Matrix.diagonal (fun w => (φ w : ℂ) * star (φ w : ℂ)) = 1
    rw [heq]
    change Matrix.diagonal (fun _ : W => (1 : ℂ)) = 1
    exact Matrix.diagonal_one⟩

/-- A signal-sector phase of the form exp(i θ (2Π-I)). -/
def signalPhase {S D : Type*} (s₀ : S) [DecidableEq S] (θ : ℝ) : S × D → Circle :=
  fun w => Circle.exp (if w.1 = s₀ then θ else -θ)

/-- Actual alternating U/U-adjoint oracle calls, each followed by a known
unitary phase. The list is independent of either oracle's matrix entries. -/
def phaseQueryTail (port : QueryPort A W) : Bool → List (W → Circle) → QueryCircuit A B W
  | _, [] => []
  | adj, φ :: phases => .matrixCall port adj :: .work (diagonalPhase φ) ::
      phaseQueryTail port (!adj) phases

/-- The initial phase and d query/phase pairs form d+1 work instructions. -/
def phaseQueryCircuit (port : QueryPort A W) (φ₀ : W → Circle)
    (phases : List (W → Circle)) : QueryCircuit A B W :=
  .work (diagonalPhase φ₀) :: phaseQueryTail port false phases

/-- Count work instructions, without claiming elementary-gate synthesis. -/
def workInstructions : QueryCircuit A B W → ℕ
  | [] => 0
  | .work _ :: rest => workInstructions rest + 1
  | _ :: rest => workInstructions rest

omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
theorem phaseQueryTail_matrixQueries (port : QueryPort A W) (adj : Bool)
    (phases : List (W → Circle)) :
    (phaseQueryTail (B := B) port adj phases).matrixQueries = phases.length := by
  induction phases generalizing adj with
  | nil => rfl
  | cons φ phases ih => simp [phaseQueryTail, QueryCircuit.matrixQueries, ih]

omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
theorem phaseQueryTail_vectorQueries (port : QueryPort A W) (adj : Bool)
    (phases : List (W → Circle)) :
    (phaseQueryTail (B := B) port adj phases).vectorQueries = 0 := by
  induction phases generalizing adj with
  | nil => rfl
  | cons φ phases ih => simp [phaseQueryTail, QueryCircuit.vectorQueries, ih]

omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
theorem phaseQueryTail_workInstructions (port : QueryPort A W) (adj : Bool)
    (phases : List (W → Circle)) :
    workInstructions (phaseQueryTail (B := B) port adj phases) = phases.length := by
  induction phases generalizing adj with
  | nil => rfl
  | cons φ phases ih => simp [phaseQueryTail, workInstructions, ih]

/-- Exact matrix-query count, zero vector queries, exact work-word length. -/
theorem phaseQueryCircuit_counts (port : QueryPort A W) (φ₀ : W → Circle)
    (phases : List (W → Circle)) :
    (phaseQueryCircuit (B := B) port φ₀ phases).matrixQueries = phases.length ∧
    (phaseQueryCircuit (B := B) port φ₀ phases).vectorQueries = 0 ∧
    workInstructions (phaseQueryCircuit (B := B) port φ₀ phases) = phases.length + 1 := by
  simp [phaseQueryCircuit, QueryCircuit.matrixQueries, QueryCircuit.vectorQueries,
    workInstructions, phaseQueryTail_matrixQueries, phaseQueryTail_vectorQueries,
    phaseQueryTail_workInstructions]

/-- Concrete semantics, in the execution order of OracleCircuit. -/
theorem phaseQueryTail_eval_cons (port : QueryPort A W) (adj : Bool)
    (φ : W → Circle) (phases : List (W → Circle))
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (phaseQueryTail port adj (φ :: phases)).eval UA Ub =
      (phaseQueryTail port (!adj) phases).eval UA Ub * diagonalPhase φ *
        port.apply (if adj then UA⁻¹ else UA) := by
  rfl

/-- Independence applies to the complete implemented unitary, not merely
its output on an initialized input vector. -/
theorem phaseQueryCircuit_independent_vector (port : QueryPort A W) (φ₀ : W → Circle)
    (phases : List (W → Circle)) (UA : Matrix.unitaryGroup A ℂ)
    (Ub Vb : Matrix.unitaryGroup B ℂ) :
    (phaseQueryCircuit port φ₀ phases).eval UA Ub =
      (phaseQueryCircuit port φ₀ phases).eval UA Vb :=
  QueryCircuit.eval_independent_vector_oracle _ (phaseQueryCircuit_counts port φ₀ phases).2.1
    UA Ub Vb

end OptimalQLS.PolynomialTransform
