import OptimalQLS.Reduction.GenericSolver.FreshCopiesProcess

/-! Classical continuation and structural resource bounds of the same physical tree. -/
noncomputable section
open scoped Classical BigOperators
namespace OptimalQLS.Reduction.GenericSolver.FreshCopies
open Matrix LowerBounds
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
variable {A B VA VB : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable {argumentsA : A ≃ (VA → Bool)} {argumentsB : B ≃ (VB → Bool)} {O O' R : Register}

namespace Process

def bindOutput : {R : Register} → Process argumentsA argumentsB O R →
    (Bool → Process argumentsA argumentsB O' O) → Process argumentsA argumentsB O' R
  | _,.unitary U h p,next => .unitary U h (p.bindOutput next)
  | _,.matrix p adj L rest,next => .matrix p adj L (rest.bindOutput next)
  | _,.vector p adj L rest,next => .vector p adj L (rest.bindOutput next)
  | _,.measure i rest,next => .measure i (fun b=>(rest b).bindOutput next)
  | _,.trace F rest,next => .trace F (rest.bindOutput next)
  | _,.output flag,next => next flag

theorem lower_bindOutput (p : Process argumentsA argumentsB O R)
    (next : Bool → Process argumentsA argumentsB O' O) :
    (p.bindOutput next).lower=Reduction.bindOutput p.lower (fun b=>(next b).lower) := by
  induction p with
  | unitary U h p ih => simp [bindOutput,lower,Reduction.bindOutput,ih]
  | matrix p adj L rest ih => simp [bindOutput,lower,Reduction.bindOutput,ih]
  | vector p adj L rest ih => simp [bindOutput,lower,Reduction.bindOutput,ih]
  | measure i rest ih => simp [bindOutput,lower,Reduction.bindOutput,ih]
  | trace F rest ih => simp [bindOutput,lower,Reduction.bindOutput,ih]
  | output flag => rfl

theorem bindOutput_work (p : Process argumentsA argumentsB O R)
    (next : Bool → Process argumentsA argumentsB O' O) (N : ℕ)
    (hn : ∀ b,(next b).work≤N) : (p.bindOutput next).work≤p.work+N := by
  induction p with
  | unitary U h p ih => simp only [bindOutput,work];omega
  | matrix p adj L rest ih => exact ih
  | vector p adj L rest ih => exact ih
  | measure i rest ih => simp only [bindOutput,work];have hf:=ih false;have ht:=ih true;omega
  | trace F rest ih => exact ih
  | output flag => simpa only [bindOutput,work,measurements,matrixCalls,vectorCalls,zero_add] using hn flag

theorem bindOutput_measurements (p : Process argumentsA argumentsB O R)
    (next : Bool → Process argumentsA argumentsB O' O) (N : ℕ)
    (hn : ∀ b,(next b).measurements≤N) : (p.bindOutput next).measurements≤p.measurements+N := by
  induction p with
  | unitary U h p ih => exact ih
  | matrix p adj L rest ih => exact ih
  | vector p adj L rest ih => exact ih
  | measure i rest ih => simp only [bindOutput,measurements];have hf:=ih false;have ht:=ih true;omega
  | trace F rest ih => exact ih
  | output flag => simpa only [bindOutput,work,measurements,matrixCalls,vectorCalls,zero_add] using hn flag

theorem bindOutput_matrixCalls (p : Process argumentsA argumentsB O R)
    (next : Bool → Process argumentsA argumentsB O' O) (N : ℕ)
    (hn : ∀ b,(next b).matrixCalls≤N) : (p.bindOutput next).matrixCalls≤p.matrixCalls+N := by
  induction p with
  | unitary U h p ih => exact ih
  | matrix p adj L rest ih => simp only [bindOutput,matrixCalls];omega
  | vector p adj L rest ih => exact ih
  | measure i rest ih => simp only [bindOutput,matrixCalls];have hf:=ih false;have ht:=ih true;omega
  | trace F rest ih => exact ih
  | output flag => simpa only [bindOutput,work,measurements,matrixCalls,vectorCalls,zero_add] using hn flag

theorem bindOutput_vectorCalls (p : Process argumentsA argumentsB O R)
    (next : Bool → Process argumentsA argumentsB O' O) (N : ℕ)
    (hn : ∀ b,(next b).vectorCalls≤N) : (p.bindOutput next).vectorCalls≤p.vectorCalls+N := by
  induction p with
  | unitary U h p ih => exact ih
  | matrix p adj L rest ih => exact ih
  | vector p adj L rest ih => simp only [bindOutput,vectorCalls];omega
  | measure i rest ih => simp only [bindOutput,vectorCalls];have hf:=ih false;have ht:=ih true;omega
  | trace F rest ih => exact ih
  | output flag => simpa only [bindOutput,work,measurements,matrixCalls,vectorCalls,zero_add] using hn flag

end Process
end OptimalQLS.Reduction.GenericSolver.FreshCopies
