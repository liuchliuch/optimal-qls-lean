import OptimalQLS.Reduction.GenericSolver.FreshCopiesProcessTensorMatrices
import OptimalQLS.Reduction.GenericSolver.FreshCopiesProcessBind
import OptimalQLS.Reduction.GenericSolver.FreshCopiesBind

/-! Density and actual successful-leaf semantics of physical spectator tensoring. -/
noncomputable section
open scoped Classical BigOperators Kronecker
namespace OptimalQLS.Reduction.GenericSolver.FreshCopies
open Matrix LowerBounds
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
variable {A B VA VB : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable {argumentsA : A ≃ (VA → Bool)} {argumentsB : B ≃ (VB → Bool)}
variable {O O' R : Register}

namespace Process

theorem tensor_density (T : Register) (p : Process argumentsA argumentsB O R)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (select : Bool → Bool) (x : Fin R.dimension → ℂ) (z : Fin T.dimension → ℂ) :
    (p.tensor T).lower.executeDensity UA Ub select (tensorVector x z) =
      (p.lower.executeDensity UA Ub select x ⊗ₖ pureDensity z).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm := by
  induction p with
  | unitary U h p ih =>
    simp only [tensor,lower,FiniteOracleProgram.executeDensity,indexedMatrix_place,
      tensorRect_mulVec,Fin.sum_univ_one]
    rw [tensorRect_mulVec]
    exact ih _
  | matrix p adj L next ih =>
    simp only [tensor,lower,FiniteOracleProgram.executeDensity,indexedPort_tensor,tensorRect_mulVec]
    rw [tensorRect_mulVec]
    exact ih _
  | vector p adj L next ih =>
    simp only [tensor,lower,FiniteOracleProgram.executeDensity,indexedPort_tensor,tensorRect_mulVec]
    rw [tensorRect_mulVec]
    exact ih _
  | measure i next ih =>
    simp only [tensor,lower,FiniteOracleProgram.executeDensity,indexedMeasuredBit_tensor,
      tensorRect_mulVec]
    conv_lhs => arg 2; ext b; rw [tensorRect_mulVec,ih]
    ext i j
    simp [Matrix.sum_apply,Matrix.kronecker_apply,Finset.sum_mul,add_mul] <;> rfl
  | trace F next ih =>
    simp only [tensor,lower,FiniteOracleProgram.executeDensity,TensorLayout.indexedKraus_product,
      tensorRect_mulVec]
    conv_lhs => arg 2; ext b; rw [tensorRect_mulVec,ih]
    ext i j
    simp [Matrix.sum_apply,Matrix.kronecker_apply,Finset.sum_mul,add_mul] <;> rfl
  | output flag =>
    simp only [tensor,lower,FiniteOracleProgram.executeDensity]
    split_ifs
    · exact pureDensity_tensorVector x z
    · simp

/-- Arbitrary finite continuations see exactly the tensor product of the source's
actual terminal ket and the unchanged spectator ket. -/
theorem tensor_lower_bind_returns {d : ℕ}
    (T : Register) (P : (Fin d → ℂ) → Prop) (Q : (Fin O.dimension → ℂ) → Prop)
    (p : Process argumentsA argumentsB O R)
    (next : Bool → FiniteOracleProgram A B d (O.dimension*T.dimension))
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (z : Fin T.dimension → ℂ) (x : Fin R.dimension → ℂ)
    (h : Returns Q UA Ub p.lower x)
    (hn : ∀ flag v,(flag=true→Q v)→Returns P UA Ub (next flag) (tensorVector v z)) :
    Returns P UA Ub (Reduction.bindOutput (p.tensor T).lower next) (tensorVector x z) := by
  induction p with
  | unitary U hl p ih =>
    intro i
    rw [indexedMatrix_place,tensorRect_mulVec]
    exact ih _ (h i)
  | matrix p adj L rest ih =>
    simp only [tensor,lower,Reduction.bindOutput,Returns,indexedPort_tensor,tensorRect_mulVec]
    rw [tensorRect_mulVec]
    exact ih _ h
  | vector p adj L rest ih =>
    simp only [tensor,lower,Reduction.bindOutput,Returns,indexedPort_tensor,tensorRect_mulVec]
    rw [tensorRect_mulVec]
    exact ih _ h
  | measure i rest ih =>
    simp only [tensor,lower,Reduction.bindOutput,Returns]
    intro j
    rw [indexedMeasuredBit_tensor,tensorRect_mulVec]
    exact ih _ _ (h j)
  | trace F rest ih =>
    intro j
    rw [TensorLayout.indexedKraus_product,tensorRect_mulVec]
    exact ih _ (h j)
  | output flag => exact hn flag x h

/-- Physical continuations preserve successful-leaf ket guarantees. -/
theorem tensor_bind_returns (T : Register)
    (P : (Fin O'.dimension → ℂ) → Prop) (Q : (Fin O.dimension → ℂ) → Prop)
    (p : Process argumentsA argumentsB O R)
    (next : Bool → Process argumentsA argumentsB O' (O.product T))
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (z : Fin T.dimension → ℂ) (x : Fin R.dimension → ℂ)
    (h : Returns Q UA Ub p.lower x)
    (hn : ∀ flag v,(flag=true→Q v)→Returns P UA Ub (next flag).lower (tensorVector v z)) :
    Returns P UA Ub ((p.tensor T).bindOutput next).lower (tensorVector x z) := by
  rw [lower_bindOutput]
  exact tensor_lower_bind_returns T P Q p (fun flag=>(next flag).lower) UA Ub z x h hn

/-- Density transport through arbitrary continuations, retaining the two source
output flags separately. -/
theorem tensor_lower_bind_density {d : ℕ} (T : Register)
    (p : Process argumentsA argumentsB O R)
    (next : Bool → FiniteOracleProgram A B d (O.dimension*T.dimension))
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (select : Bool → Bool)
    (L : Bool → Matrix (Fin O.dimension) (Fin O.dimension) ℂ →ₗ[ℝ]
      Matrix (Fin d) (Fin d) ℂ)
    (z : Fin T.dimension → ℂ)
    (hL : ∀ flag x,(next flag).executeDensity UA Ub select (tensorVector x z)=L flag (pureDensity x))
    (x : Fin R.dimension → ℂ) :
    (Reduction.bindOutput (p.tensor T).lower next).executeDensity UA Ub select (tensorVector x z)=
      L true (p.lower.executeDensity UA Ub id x)+L false (p.lower.executeDensity UA Ub Bool.not x) := by
  induction p with
  | unitary U h p ih =>
    simp only [tensor,lower,Reduction.bindOutput,FiniteOracleProgram.executeDensity,
      indexedMatrix_place,tensorRect_mulVec,Fin.sum_univ_one]
    rw [tensorRect_mulVec]
    exact ih _
  | matrix p adj L next ih =>
    simp only [tensor,lower,Reduction.bindOutput,FiniteOracleProgram.executeDensity,
      indexedPort_tensor,tensorRect_mulVec]
    rw [tensorRect_mulVec]
    exact ih _
  | vector p adj L next ih =>
    simp only [tensor,lower,Reduction.bindOutput,FiniteOracleProgram.executeDensity,
      indexedPort_tensor,tensorRect_mulVec]
    rw [tensorRect_mulVec]
    exact ih _
  | measure i next ih =>
    simp only [tensor,lower,Reduction.bindOutput,FiniteOracleProgram.executeDensity,
      indexedMeasuredBit_tensor]
    conv_lhs => arg 2; ext b; rw [tensorRect_mulVec,ih]
    simp only [map_sum,Finset.sum_add_distrib] <;> rfl
  | trace F next ih =>
    simp only [tensor,lower,Reduction.bindOutput,FiniteOracleProgram.executeDensity,
      TensorLayout.indexedKraus_product]
    conv_lhs => arg 2; ext b; rw [tensorRect_mulVec,ih]
    simp only [map_sum,Finset.sum_add_distrib] <;> rfl
  | output flag => cases flag <;> simp [tensor,lower,Reduction.bindOutput,FiniteOracleProgram.executeDensity,hL]

theorem tensor_bind_density (T : Register) (p : Process argumentsA argumentsB O R)
    (next : Bool → Process argumentsA argumentsB O' (O.product T))
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (select : Bool → Bool)
    (L : Bool → Matrix (Fin O.dimension) (Fin O.dimension) ℂ →ₗ[ℝ]
      Matrix (Fin O'.dimension) (Fin O'.dimension) ℂ)
    (z : Fin T.dimension → ℂ)
    (hL : ∀ flag x,(next flag).lower.executeDensity UA Ub select (tensorVector x z)=L flag (pureDensity x))
    (x : Fin R.dimension → ℂ) :
    ((p.tensor T).bindOutput next).lower.executeDensity UA Ub select (tensorVector x z)=
      L true (p.lower.executeDensity UA Ub id x)+L false (p.lower.executeDensity UA Ub Bool.not x) := by
  rw [lower_bindOutput]
  exact tensor_lower_bind_density T p (fun flag=>(next flag).lower) UA Ub select L z hL x

end Process
end OptimalQLS.Reduction.GenericSolver.FreshCopies
