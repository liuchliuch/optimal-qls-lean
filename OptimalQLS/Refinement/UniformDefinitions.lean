import OptimalQLS.Refinement.RunCorrectness
import OptimalQLS.PhysicalPadding.Polynomial

/-! # Uniform selection of an actual one-run two-oracle solver -/
noncomputable section
namespace OptimalQLS.Refinement
open Matrix Preparation Alignment TransducerCompiler BinaryClock PolynomialTransform PhysicalPadding
open scoped Matrix.Norms.L2Operator
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1000000

abbrev PhysicalRunSpace (a d : ℕ) (κ : ℝ) := Space
  (CoarseAux (GraphEncoding.PhysicalSignal (Bits a)) (preparationExponent κ))
  (PolynomialTransform.PhysicalSignal (a+4)) (PolynomialTransform.PhysicalSignal a) (PhysicalData d)


def selectedRun {a d : ℕ} (cf : GraphAttachedCircuit a (PhysicalData d) (PhysicalData d))
    (cc : SingleFlagCircuit a (PhysicalData d) (PhysicalData d))
    {κ ŝ : ℝ} (hκ : 2≤κ) (hlo : 3/8≤ŝ) (hhi : ŝ≤5*κ/2) :
    QueryCircuit (Bits a × PhysicalData d) (PhysicalData d) (PhysicalRunSpace a d κ) :=
  fullRunProgram (selectedPreparationCircuit (fun _ : Fin a=>false) (0 : PhysicalData d) hκ hlo hhi)
    (cf.toQuery (GraphAttachedGate.eval a)) (cc.toQuery (SingleFlagGate.eval a))


def selectedRunBasis (a d : ℕ) (κ : ℝ) : PhysicalRunSpace a d κ :=
  runBasisIndex (GraphEncoding.physicalSignalZero (fun _ : Fin a=>false)) (0 : PhysicalData d)
    (physicalZero (a+4)) (physicalZero a) (preparationExponent κ)


def selectedRunAccept (a d : ℕ) (κ : ℝ) : PhysicalData d ↪ PhysicalRunSpace a d κ where
  toFun i := (physicalZero a,(coarseZero (GraphEncoding.physicalSignalZero (fun _ : Fin a=>false))
    (preparationExponent κ),(physicalZero (a+4),(2,i))))
  inj' := by intro i j h; exact congrArg (fun p=>p.2.2.2.2) h


end OptimalQLS.Refinement
