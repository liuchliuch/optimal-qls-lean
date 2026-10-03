import OptimalQLS.Reduction.GenericSolver.FreshCopiesDiscard

/-! A coherent two-outcome accepted-coordinate measurement followed solely by
partial trace of unused factors. For the reduction embedding it is one literal
head-qubit measurement. No data reset is performed. -/
noncomputable section
open scoped Classical BigOperators
namespace OptimalQLS.Reduction.GenericSolver.FreshCopies
open Matrix LowerBounds Refinement.Repetition
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable {d m : ℕ}

def rejectProjection (e : Fin d ↪ Fin m) : Matrix (Fin m) (Fin m) ℂ :=
  diagonal (fun j=>if ∃ i,e i=j then 0 else 1)

theorem rejectProjection_mulVec (e : Fin d ↪ Fin m) (v : Fin m → ℂ) :
    rejectProjection e*ᵥv=rejectAmplitude e v := by
  ext j
  simp [rejectProjection,Matrix.mulVec,dotProduct,Matrix.diagonal, rejectAmplitude]

theorem head_complete (e : Fin d ↪ Fin m) :
    (acceptMatrix e)ᴴ*acceptMatrix e+(rejectProjection e)ᴴ*rejectProjection e=1 := by
  ext i j
  by_cases hij:i=j
  · subst j
    by_cases h:∃k,e k=i
    · obtain ⟨k,rfl⟩:=h
      simp [acceptMatrix,rejectProjection,Matrix.mul_apply,Matrix.conjTranspose_apply,
        Matrix.diagonal,e.injective.eq_iff]
    · have hn:∀k,e k≠i:=fun k hk=>h ⟨k,hk⟩
      simp [acceptMatrix,rejectProjection,Matrix.mul_apply,Matrix.conjTranspose_apply,
        Matrix.diagonal,h,hn]
  · have hzero(k:Fin d):(if e k=i then (1:ℂ) else 0)*(if e k=j then 1 else 0)=0 := by
      split_ifs <;> simp_all
    simp [acceptMatrix,rejectProjection,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Matrix.diagonal,hij,Ne.symm hij,hzero]

def headDimension (d m : ℕ) : Fin 2 → ℕ := Fin.cases d (fun _=>m)

def headKraus (e : Fin d ↪ Fin m) : (i : Fin 2) → Matrix (Fin (headDimension d m i)) (Fin m) ℂ :=
  Fin.cases (acceptMatrix e) (fun _=>rejectProjection e)

theorem head_normalized (e : Fin d ↪ Fin m) : ∑ i,(headKraus e i)ᴴ*headKraus e i=1 := by
  rw [Fin.sum_univ_succ,Fin.sum_univ_one]
  exact head_complete e

/-- The accepted output traces the unused fresh pool; the rejected outcome
traces the used active factor and proceeds on the untouched pool. -/
def headExtract {r : ℕ} (e : Fin d ↪ Fin m) (next : FiniteOracleProgram A B d r) :
    FiniteOracleProgram A B d (m*r) :=
  .instrument 2 (fun i=>headDimension d m i*r) (fun i=>tensorRect r (headKraus e i))
    (tensorRect_normalized _ _ (head_normalized e) r)
    (Fin.cases (discardSecond (.output true false)) (fun _=>discardFirst m next))

theorem headExtract_density {r : ℕ} (e : Fin d ↪ Fin m) (out : Fin d)
    (next : FiniteOracleProgram A B d r) (UA : Matrix.unitaryGroup A ℂ)
    (Ub : Matrix.unitaryGroup B ℂ) (select : Bool → Bool) (x : Fin m → ℂ) (z : Fin r → ℂ) :
    (headExtract e next).executeDensity UA Ub select (tensorVector x z)=
      (if select true then bornMass z • pureDensity (fun i=>x (e i)) else 0)+
      (bornMass x-bornMass (fun i=>x (e i))) • next.executeDensity UA Ub select z := by
  simp only [headExtract,FiniteOracleProgram.executeDensity,Fin.sum_univ_succ,Fin.sum_univ_one,
    headKraus,Fin.cases_zero,Fin.cases_succ,tensorRect_mulVec]
  rw [discardSecond_density,discardFirst_density,acceptMatrix_mulVec,rejectProjection_mulVec]
  have hr:bornMass (rejectAmplitude e x)=bornMass x-bornMass (fun i=>x (e i)) :=
    rejection_mass e (e out) x
  rw [hr]
  simp only [FiniteOracleProgram.executeDensity]
  split_ifs <;> simp
  rfl

end OptimalQLS.Reduction.GenericSolver.FreshCopies
