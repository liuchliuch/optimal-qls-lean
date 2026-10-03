import OptimalQLS.Reduction.GenericSolver.FreshCopiesHead

/-! Tensor spectator continuations preserve actual successful-leaf guarantees,
not just the aggregate density matrix. -/
noncomputable section
open scoped BigOperators
namespace OptimalQLS.Reduction.GenericSolver.FreshCopies
open Matrix LowerBounds Refinement.Repetition
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable {d m w r : ℕ}

theorem tensor_bind_density (tree : FiniteOracleProgram A B m w)
    (next : Bool → FiniteOracleProgram A B d (m*r))
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (select : Bool → Bool)
    (L : Bool → Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ)
    (z : Fin r → ℂ)
    (hL : ∀ flag x,(next flag).executeDensity UA Ub select (tensorVector x z)=L flag (pureDensity x))
    (x : Fin w → ℂ) :
    (bindOutput (tensorProgram r tree) next).executeDensity UA Ub select (tensorVector x z)=
      L true (tree.executeDensity UA Ub id x)+L false (tree.executeDensity UA Ub Bool.not x) := by
  induction tree with
  | output flag aborted => cases flag <;> simp [tensorProgram,bindOutput,FiniteOracleProgram.executeDensity,hL]
  | matrixQuery p adj tree ih =>
    simp only [tensorProgram,bindOutput,FiniteOracleProgram.executeDensity,tensorPort_apply,tensorRect_mulVec]
    exact ih _
  | vectorQuery p adj tree ih =>
    simp only [tensorProgram,bindOutput,FiniteOracleProgram.executeDensity,tensorPort_apply,tensorRect_mulVec]
    exact ih _
  | instrument k dims K hn tree ih =>
    simp only [tensorProgram,bindOutput,FiniteOracleProgram.executeDensity,tensorRect_mulVec,ih,
      map_sum,Finset.sum_add_distrib]

theorem tensor_bind_returns (P : (Fin d → ℂ) → Prop) (Q : (Fin m → ℂ) → Prop)
    (tree : FiniteOracleProgram A B m w) (next : Bool → FiniteOracleProgram A B d (m*r))
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (z : Fin r → ℂ) (x : Fin w → ℂ) (h : Returns Q UA Ub tree x)
    (hn : ∀ flag v,(flag=true→Q v)→Returns P UA Ub (next flag) (tensorVector v z)) :
    Returns P UA Ub (bindOutput (tensorProgram r tree) next) (tensorVector x z) := by
  induction tree with
  | output flag aborted => exact hn flag x h
  | matrixQuery p adj tree ih =>
    simp only [tensorProgram,bindOutput,Returns,tensorPort_apply,tensorRect_mulVec]
    exact ih _ h
  | vectorQuery p adj tree ih =>
    simp only [tensorProgram,bindOutput,Returns,tensorPort_apply,tensorRect_mulVec]
    exact ih _ h
  | instrument k dims K hc tree ih =>
    intro i
    rw [tensorRect_mulVec]
    exact ih i _ (h i)

theorem returns_discardFirst (P : (Fin d → ℂ) → Prop)
    (hP : ∀ v (c : ℂ),P v→P (c • v)) (next : FiniteOracleProgram A B d r)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (x : Fin m → ℂ) (z : Fin r → ℂ) (h : Returns P UA Ub next z) :
    Returns P UA Ub (discardFirst m next) (tensorVector x z) := by
  intro j
  rw [discardFirst_tensorVector]
  exact returns_smul P hP next UA Ub z h (x j)

theorem returns_discardSecond (P : (Fin d → ℂ) → Prop)
    (hP : ∀ v (c : ℂ),P v→P (c • v)) (next : FiniteOracleProgram A B d d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (x : Fin d → ℂ) (z : Fin r → ℂ) (h : Returns P UA Ub next x) :
    Returns P UA Ub (discardSecond next) (tensorVector x z) := by
  intro j
  rw [discardSecond_tensorVector]
  exact returns_smul P hP next UA Ub x h (z j)

theorem returns_headExtract (P : (Fin d → ℂ) → Prop)
    (hP : ∀ v (c : ℂ),P v→P (c • v)) (e : Fin d ↪ Fin m)
    (next : FiniteOracleProgram A B d r) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (x : Fin m → ℂ) (z : Fin r → ℂ) (h : Returns P UA Ub next z)
    (hx : P (fun i=>x (e i))) :
    Returns P UA Ub (headExtract e next) (tensorVector x z) := by
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · rw [tensorRect_mulVec]
    simp only [headKraus,Fin.cases_zero]
    rw [acceptMatrix_mulVec]
    exact returns_discardSecond P hP (.output true false) UA Ub _ z (fun _=>hx)
  · rw [tensorRect_mulVec]
    exact returns_discardFirst P hP next UA Ub _ z h

end OptimalQLS.Reduction.GenericSolver.FreshCopies
