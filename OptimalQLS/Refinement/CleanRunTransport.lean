import OptimalQLS.Refinement.RunRepetition
import OptimalQLS.PhysicalPadding.Basis

/-! # Exact accepting amplitudes through a proved clean circuit refinement -/
noncomputable section
namespace OptimalQLS.Refinement
open Matrix PolynomialTransform PhysicalPadding
set_option synthInstance.maxSize 8192
variable {W P A B : Type*} [Fintype W] [DecidableEq W] [Fintype P] [DecidableEq P]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] {d : ℕ}

def transportedAccept (f : W ↪ P) (e : Fin d ↪ W) : Fin d ↪ P := e.trans f

theorem clean_unitary_basis (f : W ↪ P) (U : Matrix.unitaryGroup P ℂ)
    (V : Matrix.unitaryGroup W ℂ)
    (h : U.val*basisInsertion f=basisInsertion f*V.val) (zero : W) :
    U.val*ᵥPi.single (f zero) 1=basisInsertion f*ᵥ(V.val*ᵥPi.single zero 1) := by
  rw [←basisInsertion_basis f zero,Matrix.mulVec_mulVec,h,←Matrix.mulVec_mulVec]

theorem clean_unitary_accepted (f : W ↪ P) (e : Fin d ↪ W) (U : Matrix.unitaryGroup P ℂ)
    (V : Matrix.unitaryGroup W ℂ)
    (h : U.val*basisInsertion f=basisInsertion f*V.val) (zero : W) :
    (fun i=>(U.val*ᵥPi.single (f zero) 1) (transportedAccept f e i))=
      (fun i=>(V.val*ᵥPi.single zero 1) (e i)) := by
  rw [clean_unitary_basis f U V h zero]
  funext i
  exact insertion_mulVec_active f _ (e i)

/-- A fixed clean embedding transports the actual one-run accepted vector,
including its norm, phase and success mass, by equality. -/
theorem clean_circuit_accepted (f : W ↪ P) (e : Fin d ↪ W)
    (c : QueryCircuit A B P) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (V : Matrix.unitaryGroup W ℂ)
    (h : (c.eval UA Ub).val*basisInsertion f=basisInsertion f*V.val) (zero : W) :
    acceptedVector c (transportedAccept f e) (f zero) UA Ub=
      WithLp.toLp 2 (fun i=>(V.val*ᵥPi.single zero 1) (e i)) := by
  exact congrArg (WithLp.toLp 2) (clean_unitary_accepted f e _ V h zero)

end OptimalQLS.Refinement
