import OptimalQLS.LowerBounds.QueryPolynomial
import OptimalQLS.OracleCircuit

/-!
# Concrete polynomial matrix operations and controlled query ports

Evaluation is entrywise at the actual Boolean input. Degree lemmas are proved
from finite matrix sums/products, including adjoints, controlled blocks, and
basis rewiring used by the operational query model.
-/
noncomputable section
open scoped BigOperators
namespace OptimalQLS.LowerBounds
open Matrix MvPolynomial

abbrev InputPolynomial (m : ℕ) := MvPolynomial (Fin m) ℂ

def evalMatrix {m : ℕ} {D E : Type*} (z : BitString m) (P : Matrix D E (InputPolynomial m)) : Matrix D E ℂ :=
  P.map (MvPolynomial.eval (bitValue z))

def constantPolynomialMatrix {m : ℕ} {D E : Type*} (A : Matrix D E ℂ) : Matrix D E (InputPolynomial m) :=
  A.map MvPolynomial.C

def polynomialAdjoint {m : ℕ} {D E : Type*} (P : Matrix D E (InputPolynomial m)) :
    Matrix E D (InputPolynomial m) :=
  fun i j => MvPolynomial.map (starRingEnd ℂ) (P j i)

def MatrixDegreeLE {m : ℕ} {D E : Type*} (P : Matrix D E (InputPolynomial m)) (d : ℕ) : Prop :=
  ∀ i j, (P i j).totalDegree ≤ d

@[simp] theorem evalMatrix_constant {m : ℕ} {D E : Type*} (z : BitString m) (A : Matrix D E ℂ) :
    evalMatrix z (constantPolynomialMatrix A) = A := by ext i j; simp [evalMatrix, constantPolynomialMatrix]

@[simp] theorem evalMatrix_zero {m : ℕ} {D E : Type*} (z : BitString m) :
    evalMatrix z (0 : Matrix D E (InputPolynomial m)) = 0 := by ext i j; simp [evalMatrix]

@[simp] theorem evalMatrix_one {m : ℕ} {D : Type*} [DecidableEq D] (z : BitString m) :
    evalMatrix z (1 : Matrix D D (InputPolynomial m)) = 1 := by
  ext i j; simp [evalMatrix, Matrix.one_apply, apply_ite]

@[simp] theorem evalMatrix_mul {m : ℕ} {D E F : Type*} [Fintype E]
    (z : BitString m) (P : Matrix D E (InputPolynomial m)) (Q : Matrix E F (InputPolynomial m)) :
    evalMatrix z (P * Q) = evalMatrix z P * evalMatrix z Q := by
  ext i j; simp [evalMatrix, Matrix.mul_apply, map_sum, map_mul]

@[simp] theorem evalMatrix_neg {m : ℕ} {D E : Type*} (z : BitString m) (P : Matrix D E (InputPolynomial m)) :
    evalMatrix z (-P) = -evalMatrix z P := by ext i j; simp [evalMatrix]

@[simp] theorem evalMatrix_adjoint {m : ℕ} {D E : Type*} (z : BitString m)
    (P : Matrix D E (InputPolynomial m)) :
    evalMatrix z (polynomialAdjoint P) = (evalMatrix z P).conjTranspose := by
  ext i j
  exact eval_conjugate (P j i) z

@[simp] theorem evalMatrix_submatrix {m : ℕ} {D E F G : Type*} (z : BitString m)
    (P : Matrix D E (InputPolynomial m)) (f : F → D) (g : G → E) :
    evalMatrix z (P.submatrix f g) = (evalMatrix z P).submatrix f g := rfl

@[simp] theorem evalMatrix_fromBlocks {m : ℕ} {D E F G : Type*} (z : BitString m)
    (A : Matrix D F (InputPolynomial m)) (B : Matrix D G (InputPolynomial m))
    (C : Matrix E F (InputPolynomial m)) (D' : Matrix E G (InputPolynomial m)) :
    evalMatrix z (Matrix.fromBlocks A B C D') =
      Matrix.fromBlocks (evalMatrix z A) (evalMatrix z B) (evalMatrix z C) (evalMatrix z D') := by
  ext i j; cases i <;> cases j <;> rfl

@[simp] theorem evalMatrix_blockDiagonal {m : ℕ} {D I : Type*} [DecidableEq I]
    (z : BitString m) (P : I → Matrix D D (InputPolynomial m)) :
    evalMatrix z (Matrix.blockDiagonal P) = Matrix.blockDiagonal (fun i => evalMatrix z (P i)) := by
  ext i j
  by_cases h : i.2 = j.2 <;> simp [evalMatrix, Matrix.blockDiagonal_apply, h]

theorem matrixDegree_constant {m d : ℕ} {D E : Type*} (A : Matrix D E ℂ) :
    MatrixDegreeLE (constantPolynomialMatrix (m := m) A) d := by intro i j; simp [constantPolynomialMatrix]

theorem matrixDegree_zero {m d : ℕ} {D E : Type*} :
    MatrixDegreeLE (0 : Matrix D E (InputPolynomial m)) d := by intro i j; simp

theorem matrixDegree_one {m d : ℕ} {D : Type*} [DecidableEq D] :
    MatrixDegreeLE (1 : Matrix D D (InputPolynomial m)) d := by intro i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem matrixDegree_mul {m d e : ℕ} {D E F : Type*} [Fintype E]
    {P : Matrix D E (InputPolynomial m)} {Q : Matrix E F (InputPolynomial m)}
    (hP : MatrixDegreeLE P d) (hQ : MatrixDegreeLE Q e) : MatrixDegreeLE (P * Q) (d + e) := by
  intro i j
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k _
  exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (hP i k) (hQ k j))

theorem matrixDegree_neg {m d : ℕ} {D E : Type*} {P : Matrix D E (InputPolynomial m)}
    (hP : MatrixDegreeLE P d) : MatrixDegreeLE (-P) d := by
  intro i j
  simpa using hP i j

theorem matrixDegree_adjoint {m d : ℕ} {D E : Type*} {P : Matrix D E (InputPolynomial m)}
    (hP : MatrixDegreeLE P d) : MatrixDegreeLE (polynomialAdjoint P) d := by
  intro i j
  exact (totalDegree_conjugate_le (P j i)).trans (hP j i)

theorem matrixDegree_submatrix {m d : ℕ} {D E F G : Type*} {P : Matrix D E (InputPolynomial m)}
    (hP : MatrixDegreeLE P d) (f : F → D) (g : G → E) : MatrixDegreeLE (P.submatrix f g) d :=
  fun i j => hP (f i) (g j)

theorem matrixDegree_fromBlocks {m d : ℕ} {D E F G : Type*}
    {A : Matrix D F (InputPolynomial m)} {B : Matrix D G (InputPolynomial m)}
    {C : Matrix E F (InputPolynomial m)} {D' : Matrix E G (InputPolynomial m)}
    (hA : MatrixDegreeLE A d) (hB : MatrixDegreeLE B d)
    (hC : MatrixDegreeLE C d) (hD : MatrixDegreeLE D' d) : MatrixDegreeLE (Matrix.fromBlocks A B C D') d := by
  intro i j
  cases i <;> cases j <;> first | exact hA _ _ | exact hB _ _ | exact hC _ _ | exact hD _ _

theorem matrixDegree_blockDiagonal {m d : ℕ} {D I : Type*} [DecidableEq I]
    {P : I → Matrix D D (InputPolynomial m)} (hP : ∀ i, MatrixDegreeLE (P i) d) :
    MatrixDegreeLE (Matrix.blockDiagonal P) d := by
  intro i j
  simp only [Matrix.blockDiagonal_apply]
  split_ifs
  · exact hP _ _ _
  · simp

/-- Polynomial entries of the actual controlled/adjoint/rewired query-port matrix. -/
def polynomialPort {m : ℕ} {S W : Type*} [DecidableEq S]
    (port : OptimalQLS.QueryPort S W) (adjoint : Bool) (P : Matrix S S (InputPolynomial m)) :
    Matrix W W (InputPolynomial m) :=
  (Matrix.blockDiagonal (fun j : Fin port.multiplicity =>
    if port.control j then (if adjoint then polynomialAdjoint P else P) else 1)).submatrix
      port.wiring.symm port.wiring.symm

theorem polynomialPort_eval {m : ℕ} {S W : Type*} [Fintype S] [DecidableEq S]
    [Fintype W] [DecidableEq W] (port : OptimalQLS.QueryPort S W) (adjoint : Bool)
    (P : Matrix S S (InputPolynomial m)) (U : Matrix.unitaryGroup S ℂ) (z : BitString m)
    (hP : evalMatrix z P = (U : Matrix S S ℂ)) :
    evalMatrix z (polynomialPort port adjoint P) =
      (port.apply (if adjoint then U⁻¹ else U) : Matrix W W ℂ) := by
  unfold polynomialPort
  rw [evalMatrix_submatrix, evalMatrix_blockDiagonal]
  have heq : (fun j : Fin port.multiplicity =>
      evalMatrix z (if port.control j then (if adjoint then polynomialAdjoint P else P) else 1)) =
      (fun j : Fin port.multiplicity => if port.control j then
        ((if adjoint then U⁻¹ else U : Matrix.unitaryGroup S ℂ) : Matrix S S ℂ) else 1) := by
    funext j
    cases port.control j <;> cases adjoint <;>
      simp only [Bool.false_eq_true, if_false, if_true, evalMatrix_one,
        evalMatrix_adjoint, hP, Matrix.UnitaryGroup.inv_val, Matrix.star_eq_conjTranspose]
  rw [heq]
  cases adjoint <;> rfl

theorem polynomialPort_degree {m d : ℕ} {S W : Type*} [DecidableEq S]
    (port : OptimalQLS.QueryPort S W) (adjoint : Bool) {P : Matrix S S (InputPolynomial m)}
    (hP : MatrixDegreeLE P d) : MatrixDegreeLE (polynomialPort port adjoint P) d := by
  apply matrixDegree_submatrix
  apply matrixDegree_blockDiagonal
  intro j
  cases port.control j
  · exact matrixDegree_one
  · cases adjoint
    · exact hP
    · exact matrixDegree_adjoint hP

end OptimalQLS.LowerBounds
