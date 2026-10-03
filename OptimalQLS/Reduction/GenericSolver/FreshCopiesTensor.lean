import OptimalQLS.Reduction.GenericSolver.BranchwiseMixture
import OptimalQLS.PolynomialTransform.CleanTransport
import QuantumChannelStein.Kraus

/-! Literal spectator tensoring, including arbitrary rectangular instruments.
This is the operational basis for running a supplied solver on fresh copies. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Kronecker
namespace OptimalQLS.Reduction.GenericSolver.FreshCopies
open Matrix LowerBounds PolynomialTransform
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def tensorRect {w v : ℕ} (r : ℕ) (M : Matrix (Fin v) (Fin w) ℂ) :
    Matrix (Fin (v*r)) (Fin (w*r)) ℂ :=
  (M ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

def tensorVector {w r : ℕ} (x : Fin w → ℂ) (z : Fin r → ℂ) : Fin (w*r) → ℂ :=
  fun i=>x (finProdFinEquiv.symm i).1*z (finProdFinEquiv.symm i).2

theorem tensorRect_mulVec {w v r : ℕ} (M : Matrix (Fin v) (Fin w) ℂ)
    (x : Fin w → ℂ) (z : Fin r → ℂ) :
    tensorRect r M*ᵥtensorVector x z=tensorVector (M*ᵥx) z := by
  ext j
  obtain ⟨⟨i,s⟩,rfl⟩:=finProdFinEquiv.surjective j
  simp only [tensorRect,tensorVector,Matrix.mulVec,dotProduct,Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [(finProdFinEquiv (m := w) (n := r)).symm.sum_comp
    (fun p : Fin w × Fin r => (M ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℂ)) (i,s) p * (x p.1*z p.2))]
  simp [Fintype.sum_prod_type,Matrix.kronecker_apply,Matrix.one_apply,
    Finset.sum_mul,mul_assoc]

theorem tensorRect_normalized {w k : ℕ} (dims : Fin k → ℕ)
    (K : ∀ i,Matrix (Fin (dims i)) (Fin w) ℂ)
    (hn : ∑ i,(K i)ᴴ*K i=1) (r : ℕ) :
    ∑ i,(tensorRect r (K i))ᴴ*tensorRect r (K i)=1 := by
  simp_rw [tensorRect,Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,
    ←Matrix.mul_kronecker_mul,Matrix.one_mul]
  have hs : (∑ i,(((K i)ᴴ*K i) ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix
      finProdFinEquiv.symm finProdFinEquiv.symm)=
      (((∑ i,(K i)ᴴ*K i) ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm) := by
    ext x y
    simp [Matrix.sum_apply,Matrix.kronecker_apply,Finset.sum_mul]
  rw [hs,hn,Matrix.one_kronecker_one,Matrix.submatrix_one_equiv]

def tensorPort {w : ℕ} (r : ℕ) (p : QueryPort A (Fin w)) : QueryPort A (Fin (w*r)) :=
  (scratchPort (finProdFinEquiv (m := w) (n := r))).comp p

theorem tensorPort_apply {w r : ℕ} (p : QueryPort A (Fin w))
    (U : Matrix.unitaryGroup A ℂ) :
    ((tensorPort r p).apply U).val=tensorRect r (p.apply U).val := by
  rw [tensorPort,QueryPort.comp_apply,scratchPort_apply]
  ext x y
  obtain ⟨⟨i,s⟩,rfl⟩:=finProdFinEquiv.surjective x
  obtain ⟨⟨j,t⟩,rfl⟩:=finProdFinEquiv.surjective y
  rw [placeHom_entry]
  simp [tensorRect,Matrix.kronecker_apply,Matrix.one_apply]

def tensorProgram (r : ℕ) {d : ℕ} : {w : ℕ} → FiniteOracleProgram A B d w →
    FiniteOracleProgram A B (d*r) (w*r)
  | _, .output f b => .output f b
  | _, .matrixQuery p adj next => .matrixQuery (tensorPort r p) adj (tensorProgram r next)
  | _, .vectorQuery p adj next => .vectorQuery (tensorPort r p) adj (tensorProgram r next)
  | _, .instrument k dims K hn next =>
    .instrument k (fun i=>dims i*r) (fun i=>tensorRect r (K i))
      (tensorRect_normalized dims K hn r) (fun i=>tensorProgram r (next i))

theorem pureDensity_tensorVector {w r : ℕ} (x : Fin w → ℂ) (z : Fin r → ℂ) :
    pureDensity (tensorVector x z)=
      (pureDensity x ⊗ₖ pureDensity z).submatrix finProdFinEquiv.symm finProdFinEquiv.symm := by
  ext i j
  simp [pureDensity,ketBra,tensorVector,Matrix.vecMulVec,Matrix.kronecker_apply]
  ring

/-- Tensoring acts on the chosen copy and preserves every spectator, on every
instrument branch, for either successful or failing completed outcomes. -/
theorem tensorProgram_density {d w r : ℕ} (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (select : Bool → Bool) (x : Fin w → ℂ) (z : Fin r → ℂ) :
    (tensorProgram r tree).executeDensity UA Ub select (tensorVector x z)=
      (tree.executeDensity UA Ub select x ⊗ₖ pureDensity z).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm := by
  induction tree with
  | output f b =>
    simp only [tensorProgram,FiniteOracleProgram.executeDensity]
    split_ifs
    · exact pureDensity_tensorVector x z
    · simp
  | matrixQuery p adj next ih =>
    simp only [tensorProgram,FiniteOracleProgram.executeDensity,tensorPort_apply,tensorRect_mulVec]
    exact ih _
  | vectorQuery p adj next ih =>
    simp only [tensorProgram,FiniteOracleProgram.executeDensity,tensorPort_apply,tensorRect_mulVec]
    exact ih _
  | instrument k dims K hn next ih =>
    simp only [tensorProgram,FiniteOracleProgram.executeDensity,tensorRect_mulVec,ih]
    ext i j
    simp [Matrix.sum_apply,Matrix.kronecker_apply,Finset.sum_mul]

end OptimalQLS.Reduction.GenericSolver.FreshCopies
