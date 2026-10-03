import OptimalQLS.Reduction.GenericSolver.FreshCopiesTensor

/-! Actual tensor-factor partial traces. Dropping a used register exposes an
already initialized fresh copy; no conditional X/reset gates are performed. -/
noncomputable section
open scoped BigOperators
namespace OptimalQLS.Reduction.GenericSolver.FreshCopies
open Matrix LowerBounds Refinement.Repetition
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def discardFirstKraus (m r : ℕ) (j : Fin m) : Matrix (Fin r) (Fin (m*r)) ℂ :=
  fun k x=>if finProdFinEquiv.symm x=(j,k) then 1 else 0

def discardSecondKraus (m r : ℕ) (j : Fin r) : Matrix (Fin m) (Fin (m*r)) ℂ :=
  fun k x=>if finProdFinEquiv.symm x=(k,j) then 1 else 0

theorem discardFirst_normalized (m r : ℕ) :
    ∑ j,(discardFirstKraus m r j)ᴴ*discardFirstKraus m r j=1 := by
  ext x y
  obtain ⟨⟨i,s⟩,rfl⟩:=finProdFinEquiv.surjective x
  obtain ⟨⟨j,t⟩,rfl⟩:=finProdFinEquiv.surjective y
  simp [discardFirstKraus,Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
    finProdFinEquiv.injective.eq_iff,Prod.mk.injEq,Matrix.one_apply,ite_and,apply_ite]
  split_ifs <;> simp_all [eq_comm]

theorem discardSecond_normalized (m r : ℕ) :
    ∑ j,(discardSecondKraus m r j)ᴴ*discardSecondKraus m r j=1 := by
  ext x y
  obtain ⟨⟨i,s⟩,rfl⟩:=finProdFinEquiv.surjective x
  obtain ⟨⟨j,t⟩,rfl⟩:=finProdFinEquiv.surjective y
  simp [discardSecondKraus,Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
    finProdFinEquiv.injective.eq_iff,Prod.mk.injEq,Matrix.one_apply,ite_and,apply_ite]
  split_ifs <;> simp_all [eq_comm]

theorem discardFirst_mulVec {m r : ℕ} (v : Fin (m*r) → ℂ) (j : Fin m) :
    discardFirstKraus m r j*ᵥv=fun k=>v (finProdFinEquiv (j,k)) := by
  ext k
  have he (i : Fin (m*r)) : finProdFinEquiv.symm i=(j,k) ↔ i=finProdFinEquiv (j,k) := by
    constructor
    · intro h
      have ht:=congrArg (finProdFinEquiv (m := m) (n := r)) h
      rw [Equiv.apply_symm_apply] at ht
      exact ht
    · intro h; rw [h,Equiv.symm_apply_apply]
  simp only [discardFirstKraus,Matrix.mulVec,dotProduct,he,ite_mul,one_mul,zero_mul]
  simp

theorem discardSecond_mulVec {m r : ℕ} (v : Fin (m*r) → ℂ) (j : Fin r) :
    discardSecondKraus m r j*ᵥv=fun k=>v (finProdFinEquiv (k,j)) := by
  ext k
  have he (i : Fin (m*r)) : finProdFinEquiv.symm i=(k,j) ↔ i=finProdFinEquiv (k,j) := by
    constructor
    · intro h
      have ht:=congrArg (finProdFinEquiv (m := m) (n := r)) h
      rw [Equiv.apply_symm_apply] at ht
      exact ht
    · intro h; rw [h,Equiv.symm_apply_apply]
  simp only [discardSecondKraus,Matrix.mulVec,dotProduct,he,ite_mul,one_mul,zero_mul]
  simp

theorem discardFirst_tensorVector {m r : ℕ} (x : Fin m → ℂ) (z : Fin r → ℂ) (j : Fin m) :
    discardFirstKraus m r j*ᵥtensorVector x z=x j • z := by
  rw [discardFirst_mulVec]
  ext k
  simp [tensorVector]

theorem discardSecond_tensorVector {m r : ℕ} (x : Fin m → ℂ) (z : Fin r → ℂ) (j : Fin r) :
    discardSecondKraus m r j*ᵥtensorVector x z=z j • x := by
  rw [discardSecond_mulVec]
  ext k
  simp [tensorVector,mul_comm]

def discardFirst {d r : ℕ} (m : ℕ) (next : FiniteOracleProgram A B d r) :
    FiniteOracleProgram A B d (m*r) :=
  .instrument m (fun _=>r) (discardFirstKraus m r) (discardFirst_normalized m r) (fun _=>next)

def discardSecond {d r : ℕ} (next : FiniteOracleProgram A B d d) :
    FiniteOracleProgram A B d (d*r) :=
  .instrument r (fun _=>d) (discardSecondKraus d r) (discardSecond_normalized d r) (fun _=>next)

theorem discardFirst_density {d m r : ℕ} (next : FiniteOracleProgram A B d r)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (select : Bool → Bool)
    (x : Fin m → ℂ) (z : Fin r → ℂ) :
    (discardFirst m next).executeDensity UA Ub select (tensorVector x z)=
      bornMass x • next.executeDensity UA Ub select z := by
  simp only [discardFirst,FiniteOracleProgram.executeDensity,discardFirst_tensorVector,
    executeDensity_smul,←Finset.sum_smul]
  rfl

theorem discardSecond_density {d r : ℕ} (next : FiniteOracleProgram A B d d)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (select : Bool → Bool)
    (x : Fin d → ℂ) (z : Fin r → ℂ) :
    (discardSecond next).executeDensity UA Ub select (tensorVector x z)=
      bornMass z • next.executeDensity UA Ub select x := by
  simp only [discardSecond,FiniteOracleProgram.executeDensity,discardSecond_tensorVector,
    executeDensity_smul,←Finset.sum_smul]
  rfl

end OptimalQLS.Reduction.GenericSolver.FreshCopies
