import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Matrix.Block

/-!
# Concrete two-oracle query circuits

This is a query-circuit model, not a gate-efficiency certificate. Work gates
are explicit oracle-independent unitary matrices. A separate synthesis into
one- and two-qubit gates is required for the paper's extra-gate claims.
Oracle calls include controlled calls and adjoints, each charged once to
its own oracle. Tensor placement is an explicit basis equivalence.
-/

noncomputable section
namespace OptimalQLS
open Matrix

section UnitaryWiring
variable {S W : Type*} [Fintype S] [DecidableEq S] [Fintype W] [DecidableEq W]

/-- Conjugation by an actual computational-basis permutation. -/
def rewireUnitary (e : S ≃ W) (U : Matrix.unitaryGroup S ℂ) : Matrix.unitaryGroup W ℂ :=
  ⟨(U : Matrix S S ℂ).submatrix e.symm e.symm, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
    have hu : (U : Matrix S S ℂ) * (U : Matrix S S ℂ)ᴴ = 1 := U.property.2
    rw [hu]
    simp⟩

/-- Apply U on selected multiplicity sectors, identity on all other sectors.
This is a literal controlled unitary matrix. -/
def controlledUnitary (r : ℕ) (control : Fin r → Bool) (U : Matrix.unitaryGroup S ℂ) :
    Matrix.unitaryGroup (S × Fin r) ℂ :=
  ⟨Matrix.blockDiagonal (fun j : Fin r => if control j then (U : Matrix S S ℂ) else 1), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    have h : (fun j : Fin r =>
        (if control j then (U : Matrix S S ℂ) else 1) *
          (if control j then (U : Matrix S S ℂ) else 1)ᴴ) = 1 := by
      funext j
      have hu : (U : Matrix S S ℂ) * (U : Matrix S S ℂ)ᴴ = 1 := U.property.2
      cases control j <;> simp [hu]
    rw [h, Matrix.blockDiagonal_one]⟩

/-- Placement and control for one input query. The control depends only on
the workspace sector, never on an oracle's classical matrix entries. -/
structure QueryPort (S W : Type*) where
  multiplicity : ℕ
  wiring : S × Fin multiplicity ≃ W
  control : Fin multiplicity → Bool

def QueryPort.apply (p : QueryPort S W) (U : Matrix.unitaryGroup S ℂ) :
    Matrix.unitaryGroup W ℂ :=
  rewireUnitary p.wiring (controlledUnitary p.multiplicity p.control U)

theorem rewireUnitary_mul (e : S ≃ W) (U V : Matrix.unitaryGroup S ℂ) :
    rewireUnitary e (U * V) = rewireUnitary e U * rewireUnitary e V := by
  apply Subtype.ext
  change ((U : Matrix S S ℂ) * (V : Matrix S S ℂ)).submatrix e.symm e.symm =
    (U : Matrix S S ℂ).submatrix e.symm e.symm *
      (V : Matrix S S ℂ).submatrix e.symm e.symm
  rw [Matrix.submatrix_mul_equiv]

theorem rewireUnitary_one (e : S ≃ W) : rewireUnitary e (1 : Matrix.unitaryGroup S ℂ) = 1 := by
  apply Subtype.ext
  simp [rewireUnitary]

theorem controlledUnitary_mul (r : ℕ) (c : Fin r → Bool) (U V : Matrix.unitaryGroup S ℂ) :
    controlledUnitary r c (U * V) = controlledUnitary r c U * controlledUnitary r c V := by
  apply Subtype.ext
  change Matrix.blockDiagonal (fun j : Fin r => if c j then
    (U : Matrix S S ℂ) * (V : Matrix S S ℂ) else 1) =
    Matrix.blockDiagonal (fun j : Fin r => if c j then (U : Matrix S S ℂ) else 1) *
      Matrix.blockDiagonal (fun j : Fin r => if c j then (V : Matrix S S ℂ) else 1)
  rw [← Matrix.blockDiagonal_mul]
  congr 1
  funext i
  cases c i <;> simp

theorem controlledUnitary_one (r : ℕ) (c : Fin r → Bool) :
    controlledUnitary r c (1 : Matrix.unitaryGroup S ℂ) = 1 := by
  apply Subtype.ext
  change Matrix.blockDiagonal (fun j : Fin r => if c j then (1 : Matrix S S ℂ) else 1) = 1
  simp only [ite_self]
  exact Matrix.blockDiagonal_one

/-- Oracle insertion/control is a genuine group homomorphism. -/
def QueryPort.unitaryHom (p : QueryPort S W) :
    Matrix.unitaryGroup S ℂ →* Matrix.unitaryGroup W ℂ where
  toFun := p.apply
  map_one' := by simp [QueryPort.apply, controlledUnitary_one, rewireUnitary_one]
  map_mul' U V := by simp [QueryPort.apply, controlledUnitary_mul, rewireUnitary_mul]

theorem QueryPort.apply_inv (p : QueryPort S W) (U : Matrix.unitaryGroup S ℂ) :
    p.apply U⁻¹ = (p.apply U)⁻¹ := map_inv p.unitaryHom U

end UnitaryWiring

section Circuit
variable (A B W : Type*) [Fintype W] [DecidableEq W]

/-- The two oracle spaces need not coincide. -/
inductive QueryInstruction where
  | work (U : Matrix.unitaryGroup W ℂ)
  | matrixCall (port : QueryPort A W) (adjoint : Bool)
  | vectorCall (port : QueryPort B W) (adjoint : Bool)

abbrev QueryCircuit := List (QueryInstruction A B W)

variable {A B W} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def QueryInstruction.eval (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    QueryInstruction A B W → Matrix.unitaryGroup W ℂ
  | .work U => U
  | .matrixCall p adj => p.apply (if adj then UA⁻¹ else UA)
  | .vectorCall p adj => p.apply (if adj then Ub⁻¹ else Ub)

/-- Matrix semantics in execution order; all matrix entries are concrete. -/
def QueryCircuit.eval (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    QueryCircuit A B W → Matrix.unitaryGroup W ℂ
  | [] => 1
  | gate :: rest => QueryCircuit.eval UA Ub rest * gate.eval UA Ub

def QueryCircuit.matrixQueries : QueryCircuit A B W → ℕ
  | [] => 0
  | .matrixCall _ _ :: rest => QueryCircuit.matrixQueries rest + 1
  | _ :: rest => QueryCircuit.matrixQueries rest

def QueryCircuit.vectorQueries : QueryCircuit A B W → ℕ
  | [] => 0
  | .vectorCall _ _ :: rest => QueryCircuit.vectorQueries rest + 1
  | _ :: rest => QueryCircuit.vectorQueries rest

theorem QueryCircuit.eval_append (c d : QueryCircuit A B W)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (c ++ d).eval UA Ub = d.eval UA Ub * c.eval UA Ub := by
  induction c with
  | nil => simp [eval]
  | cons gate rest ih => simp [eval, ih, mul_assoc]

omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
theorem QueryCircuit.matrixQueries_append (c d : QueryCircuit A B W) :
    (c ++ d).matrixQueries = c.matrixQueries + d.matrixQueries := by
  induction c with
  | nil => simp [matrixQueries]
  | cons gate rest ih => cases gate <;> simp [matrixQueries, ih, Nat.add_right_comm]

omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
theorem QueryCircuit.vectorQueries_append (c d : QueryCircuit A B W) :
    (c ++ d).vectorQueries = c.vectorQueries + d.vectorQueries := by
  induction c with
  | nil => simp [vectorQueries]
  | cons gate rest ih => cases gate <;> simp [vectorQueries, ih, Nat.add_right_comm]

/-- No vector queries really means that changing the entire vector oracle
cannot change the implemented unitary, including its unprepared columns. -/
theorem QueryCircuit.eval_independent_vector_oracle (c : QueryCircuit A B W)
    (hc : c.vectorQueries = 0) (UA : Matrix.unitaryGroup A ℂ)
    (Ub Vb : Matrix.unitaryGroup B ℂ) : c.eval UA Ub = c.eval UA Vb := by
  induction c with
  | nil => rfl
  | cons gate rest ih =>
    cases gate with
    | work U =>
      simp only [vectorQueries] at hc
      simp only [eval, QueryInstruction.eval, ih hc]
    | matrixCall p adj =>
      simp only [vectorQueries] at hc
      simp only [eval, QueryInstruction.eval, ih hc]
    | vectorCall p adj => simp [vectorQueries] at hc

end Circuit
end OptimalQLS
