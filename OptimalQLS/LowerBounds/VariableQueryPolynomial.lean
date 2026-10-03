import OptimalQLS.LowerBounds.HistoryOraclePolynomial
import OptimalQLS.LowerBounds.CountableParity

/-!
# Literal two-oracle paths with changing finite workspace dimensions

Work/Kraus operations are actual input-independent complex matrices. Matrix
and vector calls use the parent's explicit adjoint/controlled QueryPort wiring.
The full vector oracle is fixed across the hidden family, so vector calls do
not increase hidden-input degree. No oracle matrix is replaced by a symbolic
cost certificate: evaluation and degrees are proved by operational recursion.
-/
noncomputable section
open scoped BigOperators
namespace OptimalQLS.LowerBounds
open Matrix MvPolynomial

universe u v
inductive VariableQueryPath (A : Type u) (B : Type v) : ℕ → Type (max u v) where
  | initial {w : ℕ} (v : Fin w → ℂ) : VariableQueryPath A B w
  | work {u w : ℕ} (G : Matrix (Fin w) (Fin u) ℂ) (prev : VariableQueryPath A B u) : VariableQueryPath A B w
  | matrixQuery {w : ℕ} (port : OptimalQLS.QueryPort A (Fin w)) (adjoint : Bool)
      (prev : VariableQueryPath A B w) : VariableQueryPath A B w
  | vectorQuery {w : ℕ} (port : OptimalQLS.QueryPort B (Fin w)) (adjoint : Bool)
      (prev : VariableQueryPath A B w) : VariableQueryPath A B w

def VariableQueryPath.matrixQueries {A B : Type*} {w : ℕ} : VariableQueryPath A B w → ℕ
  | .initial _ => 0
  | .work _ prev => prev.matrixQueries
  | .matrixQuery _ _ prev => prev.matrixQueries + 1
  | .vectorQuery _ _ prev => prev.matrixQueries

def VariableQueryPath.vectorQueries {A B : Type*} {w : ℕ} : VariableQueryPath A B w → ℕ
  | .initial _ => 0
  | .work _ prev => prev.vectorQueries
  | .matrixQuery _ _ prev => prev.vectorQueries
  | .vectorQuery _ _ prev => prev.vectorQueries + 1

variable {A B : Type*} {w : ℕ} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def VariableQueryPath.state (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    {w : ℕ} → VariableQueryPath A B w → Fin w → ℂ
  | _, .initial v => v
  | _, .work G prev => G *ᵥ prev.state UA Ub
  | w, .matrixQuery port adjoint prev =>
      (port.apply (if adjoint then UA⁻¹ else UA) : Matrix (Fin w) (Fin w) ℂ) *ᵥ prev.state UA Ub
  | w, .vectorQuery port adjoint prev =>
      (port.apply (if adjoint then Ub⁻¹ else Ub) : Matrix (Fin w) (Fin w) ℂ) *ᵥ prev.state UA Ub

def VariableQueryPath.polynomialState {m : ℕ} (P : Matrix A A (InputPolynomial m))
    (Ub : Matrix.unitaryGroup B ℂ) : {w : ℕ} → VariableQueryPath A B w → Fin w → InputPolynomial m
  | _, .initial v => fun i => C (v i)
  | _, .work G prev => fun i => ∑ j, C (G i j) * prev.polynomialState P Ub j
  | _, .matrixQuery port adjoint prev => fun i =>
      ∑ j, polynomialPort port adjoint P i j * prev.polynomialState P Ub j
  | w, .vectorQuery port adjoint prev => fun i =>
      ∑ j, C ((port.apply (if adjoint then Ub⁻¹ else Ub) : Matrix (Fin w) (Fin w) ℂ) i j) * prev.polynomialState P Ub j

/-- Exact Boolean evaluation gives the actual two-oracle operational state. -/
theorem VariableQueryPath.eval_polynomialState {m : ℕ} (P : Matrix A A (InputPolynomial m))
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (z : BitString m)
    (hP : evalMatrix z P = (UA : Matrix A A ℂ)) (path : VariableQueryPath A B w) (i : Fin w) :
    eval (bitValue z) (path.polynomialState P Ub i) = path.state UA Ub i := by
  induction path with
  | initial v => simp [polynomialState, state]
  | work G prev ih => simp [polynomialState, state, Matrix.mulVec, dotProduct, ih]
  | vectorQuery port adjoint prev ih => simp [polynomialState, state, Matrix.mulVec, dotProduct, ih]
  | @matrixQuery ww port adjoint prev ih =>
    have hport (i j : Fin ww) : eval (bitValue z) (polynomialPort port adjoint P i j) =
        (port.apply (if adjoint then UA⁻¹ else UA) : Matrix (Fin ww) (Fin ww) ℂ) i j :=
      congrFun (congrFun (polynomialPort_eval port adjoint P UA z hP) i) j
    simp [polynomialState, state, Matrix.mulVec, dotProduct, ih, hport]

/-- Matrix calls alone increase amplitude degree; vector calls can be arbitrarily numerous. -/
theorem VariableQueryPath.polynomialState_degree {m : ℕ} {P : Matrix A A (InputPolynomial m)}
    (hP : MatrixDegreeLE P 1) (Ub : Matrix.unitaryGroup B ℂ) (path : VariableQueryPath A B w) (i : Fin w) :
    (path.polynomialState P Ub i).totalDegree ≤ path.matrixQueries := by
  induction path with
  | initial v => simp [polynomialState, matrixQueries]
  | work G prev ih =>
    apply totalDegree_finsetSum_le
    intro j _
    exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using ih j)
  | vectorQuery port adjoint prev ih =>
    apply totalDegree_finsetSum_le
    intro j _
    exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using ih j)
  | matrixQuery port adjoint prev ih =>
    apply totalDegree_finsetSum_le
    intro j _
    apply (totalDegree_mul _ _).trans
    have hq := polynomialPort_degree port adjoint hP i j
    have ha := ih j
    change _ ≤ prev.matrixQueries + 1
    omega

def VariableQueryPath.bornWeight (path : VariableQueryPath A B w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) : ℝ :=
  ∑ i, Complex.normSq (path.state UA Ub i)

theorem VariableQueryPath.bornWeight_nonneg (path : VariableQueryPath A B w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) : 0 ≤ path.bornWeight UA Ub :=
  Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

def VariableQueryPath.weightPolynomial {m : ℕ} (path : VariableQueryPath A B w)
    (P : Matrix A A (InputPolynomial m)) (Ub : Matrix.unitaryGroup B ℂ) : InputPolynomial m :=
  ∑ i, path.polynomialState P Ub i * MvPolynomial.map (starRingEnd ℂ) (path.polynomialState P Ub i)

theorem VariableQueryPath.eval_weightPolynomial {m : ℕ} (path : VariableQueryPath A B w)
    (P : Matrix A A (InputPolynomial m)) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (z : BitString m) (hP : evalMatrix z P = (UA : Matrix A A ℂ)) :
    eval (bitValue z) (path.weightPolynomial P Ub) = (path.bornWeight UA Ub : ℂ) := by
  simp only [weightPolynomial, map_sum, map_mul, eval_conjugate,
    VariableQueryPath.eval_polynomialState P UA Ub z hP]
  simp [bornWeight, Complex.mul_conj]

theorem VariableQueryPath.weightPolynomial_degree {m : ℕ} (path : VariableQueryPath A B w)
    {P : Matrix A A (InputPolynomial m)} (hP : MatrixDegreeLE P 1) (Ub : Matrix.unitaryGroup B ℂ) :
    (path.weightPolynomial P Ub).totalDegree ≤ 2 * path.matrixQueries := by
  apply totalDegree_finsetSum_le
  intro i _
  apply (totalDegree_mul _ _).trans
  have h1 := path.polynomialState_degree hP Ub i
  have h2 := totalDegree_conjugate_le (path.polynomialState P Ub i)
  omega

/-- The real full-parity coefficient of any short operational two-oracle path vanishes. -/
theorem VariableQueryPath.short_parity_sum_zero {m : ℕ} (path : VariableQueryPath A B w)
    (P : Matrix A A (InputPolynomial m)) (hdegree : MatrixDegreeLE P 1)
    (UA : BitString m → Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (heval : ∀ z, evalMatrix z P = (UA z : Matrix A A ℂ)) (weight : ℝ)
    (hshort : 2 * path.matrixQueries < m) :
    (∑ z : BitString m, paritySign z * (weight * path.bornWeight (UA z) Ub)) = 0 := by
  let p : InputPolynomial m := C (weight : ℂ) * path.weightPolynomial P Ub
  have hd : p.totalDegree < m := by
    apply lt_of_le_of_lt _ hshort
    apply (totalDegree_mul _ _).trans
    simpa only [totalDegree_C, zero_add] using path.weightPolynomial_degree hdegree Ub
  have hz := parityCoefficient_eq_zero_of_degree_lt p hd
  have h_eval (z : BitString m) : eval (bitValue z) p = (weight * path.bornWeight (UA z) Ub : ℝ) := by
    simp [p, path.eval_weightPolynomial P (UA z) Ub z (heval z)]
  simp only [parityCoefficient, h_eval, ← Complex.ofReal_mul, ← Complex.ofReal_sum] at hz
  exact_mod_cast hz

end OptimalQLS.LowerBounds
