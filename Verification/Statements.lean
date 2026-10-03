import OptimalQLS.Reduction.PhysicalUpperResources
import OptimalQLS.Reduction.DirectSafety
import OptimalQLS.LowerBounds.Physical.LowerBounds
import OptimalQLS.PhysicalRobustness.GeneralProgram.Safety
import OptimalQLS.PhysicalRobustness.GeneralProgram.PromiseInputs

/-!
# Reviewable specifications for the paper's main results

These propositions are written explicitly, independently of the types of the
endpoint theorems. This file imports the mathematical and operational model,
but does not import Theorem57, Physical.Theorem61, or GeneralProgram.Promise.
Review its imported definitions as well: Comparator checks consistency with
this specification, not correspondence to the informal paper.

The explicit numerical constants witness the paper's asymptotic bounds.
-/
noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix OptimalQLS OptimalQLS.LowerBounds OptimalQLS.PhysicalPadding
open OptimalQLS.TransducerCompiler OptimalQLS.TransducerCompiler.BinaryClock
open OptimalQLS.Refinement.Repetition

namespace Verification.Specification

namespace Upper
open OptimalQLS.Reduction OptimalQLS.Reduction.PhysicalUpper
open OptimalQLS.Refinement OptimalQLS.Refinement.CostedExecution

/-- The complete input-dependent conclusion, on the same selected execution. -/
def Output {p : QLSParameters} {d : ℕ} {hk : 2 ≤ p.kappa}
    (I : Implementation p d hk) (A : Matrix (Fin d) (Fin d) ℂ) (b : DataSpace d)
    (UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × PhysicalData d) ℂ)
    (Ub : Matrix.unitaryGroup (PhysicalData d) ℂ) : Prop :=
  ((promiseExecution I).vectorDepth : ℝ) < 72000000600000 * (p.kappa / solutionScale p.alpha A b) ∧
  ((promiseSyntax I).cost : ℝ) <
    300000000000000000000 * p.kappa * (p.signalQubits + 1) * Real.log (1 / p.epsilon) +
    1000000000000000000 * (p.kappa / solutionScale p.alpha A b) * (dataQubits d + 1) ∧
  (2 : ℝ) / 3 < (promiseExecution I).successProbability UA Ub (basis (initialIndex p d)) ∧
  ∃ x : PhysicalSource d, ‖x‖ = 1 ∧ ‖x - physicalSolution A b‖ ≤ p.epsilon ∧
    (promiseExecution I).conditionalOutput UA Ub (basis (initialIndex p d)) =
      pureDensity (WithLp.ofLp x)

/-- Public resource and literal gate/oracle placement conditions. -/
def Resources {p : QLSParameters} {d : ℕ} {hk : 2 ≤ p.kappa}
    (I : Implementation p d hk) : Prop :=
  DirectCosted.CoordinateSafety (PhysicalAdapter.adapted I)
    (Preparation.CompilerAttachment.preparationExponent_pos (publicBudget p hk)) 600000
    (oracleRegisterCoordinates p.signalQubits d) (physicalDataCoordinates d) ∧
  instrumentDepth (promiseExecution I) = (promiseSyntax I).cost + 1 ∧
  (matrixDepth (promiseExecution I) : ℝ) <
    1320000000000000 * p.kappa * Real.log (1 / p.epsilon) ∧
  RegisterBound (2 ^ (dataQubits d + 3 * p.signalQubits + 2 * preparationExponent p.kappa + 31))
    (promiseExecution I) ∧
  dataQubits d + 3 * p.signalQubits + 2 * preparationExponent p.kappa + 31 ≤
    dataQubits d + 3 * p.signalQubits + 2 * Nat.log2 ⌈p.kappa⌉₊ + 87

/-- Theorem 5.7: choose one implementation before A, b, and both complete oracles. -/
def Exact : Prop :=
  ∀ (p : QLSParameters) (d : ℕ) [NeZero d] (hk : 2 ≤ p.kappa),
    0 < p.epsilon → p.epsilon < 1 / 2 →
    ∃ I : Implementation p d hk, Resources I ∧
      ∀ (A : Matrix (Fin d) (Fin d) ℂ) (b : DataSpace d)
        (UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × PhysicalData d) ℂ)
        (Ub : Matrix.unitaryGroup (PhysicalData d) ℂ),
        PhysicalExactQLSPromise p A b UA Ub → Output I A b UA Ub

/-- The explicitly relaxed estimate clause of Theorem 5.7. -/
def Relaxed : Prop :=
  ∀ (p : QLSParameters) (d : ℕ) [NeZero d] (hk : 2 ≤ p.kappa),
    0 < p.epsilon → p.epsilon < 1 / 2 →
    ∃ I : Implementation p d hk, Resources I ∧
      ∀ (A : Matrix (Fin d) (Fin d) ℂ) (b : DataSpace d)
        (UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × PhysicalData d) ℂ)
        (Ub : Matrix.unitaryGroup (PhysicalData d) ℂ),
        PhysicalRelaxedQLSPromise p A b UA Ub → Output I A b UA Ub
end Upper

/-- Theorem 6.1: both lower bounds concern the same input and the same program.
The universal algorithm may branch, loop, and change its finite workspace. -/
def Lower.{r} : Prop :=
  ∀ (kappa estimate eps : ℝ), 8 ≤ kappa → 1 ≤ estimate → estimate ≤ kappa →
    0 < eps → eps ≤ Real.exp (-16) →
    ∃ (d n : ℕ) (hd : 0 < d),
      n = ⌈Real.log (d : ℝ) / Real.log 2⌉₊ ∧ physicalDimension d = 2 ^ n ∧
      (d : ℝ) ≤ 9 * kappa * Real.log (1 / eps) ∧
      (physicalDimension d : ℝ) ≤ 18 * kappa * Real.log (1 / eps) ∧
      ∀ (Node : ℕ → Type r) (w : ℕ)
        (program : QuantumProgram (SignalIndex 1 × Fin (physicalDimension d))
          (Fin (physicalDimension d)) (physicalDimension d) Node)
        (out : Fin (physicalDimension d)) (node : Node w) (psi : Fin w → ℂ),
        ‖WithLp.toLp 2 psi‖ = 1 →
        @QuantumProgram.CorrectHermitianPhysicalQLS d ⟨Nat.ne_of_gt hd⟩ Node w
          (canonicalLowerParameters kappa estimate eps) program out node psi →
        ∃ (A : Matrix (Fin d) (Fin d) ℂ) (b : DataSpace d)
          (UA : Matrix.unitaryGroup (SignalIndex 1 × Fin (physicalDimension d)) ℂ)
          (Ub : Matrix.unitaryGroup (Fin (physicalDimension d)) ℂ),
          @PhysicalExactQLSPromise d
            (canonicalLowerParameters kappa estimate eps) A b UA Ub ∧
          EntrywiseReal A ∧ A.IsHermitian ∧ ‖A‖ = 1 ∧ ‖Ring.inverse A‖ = kappa ∧
          (∀ qA : ℕ, program.PointwiseMatrixBound out UA Ub node psi qA →
            kappa * Real.log (1 / eps) / 192 ≤ (qA : ℝ)) ∧
          (∀ qb : ℕ, program.PointwiseVectorBound out UA Ub node psi qb →
            kappa / (75 * estimate) ≤ (qb : ℝ))

namespace Robust
open OptimalQLS.PhysicalRobustness OptimalQLS.PhysicalRobustness.GeneralProgram
open OptimalQLS.Reduction OptimalQLS.Refinement

/-- Theorem 7.2: the program is also chosen before the encoding error δ.
The original norm bound and factor-two estimate are in the input promise. -/
def Statement : Prop :=
  ∀ (p : QLSParameters) (d : ℕ) [NeZero d], 2 ≤ p.kappa →
    0 < p.epsilon → p.epsilon < 1 / 2 →
    ∃ I : Implementation p.signalQubits (dataQubits d) p.kappa
        (publicEstimate p.kappa p.normEstimate) p.epsilon,
      PromiseSafe I ∧ PhysicalAdapter.Safe (circuit I) ∧
      instrumentDepth (promiseExecution I) = (promiseSyntax I).cost + 1 ∧
      (matrixDepth (promiseExecution I) : ℝ) <
        534000000000000000 * p.kappa * Real.log (1 / p.epsilon) ∧
      RegisterBound (2 ^ (dataQubits d + 3 * p.signalQubits + 2 * preparationExponent (2 * p.kappa) + 31))
        (promiseExecution I) ∧
      dataQubits d + 3 * p.signalQubits + 2 * preparationExponent (2 * p.kappa) + 31 ≤
        dataQubits d + 3 * p.signalQubits + 2 * Nat.log2 ⌈2 * p.kappa⌉₊ + 87 ∧
      ∀ (δ : ℝ) (A : Matrix (Fin d) (Fin d) ℂ) (b : DataSpace d)
        (UA : Matrix.unitaryGroup (SignalIndex p.signalQubits × PhysicalData d) ℂ)
        (Ub : Matrix.unitaryGroup (PhysicalData d) ℂ),
        PhysicalApproximateQLSPromise p δ A b UA Ub →
        ((promiseExecution I).vectorDepth : ℝ) < 216000001800000 * (p.kappa / solutionScale p.alpha A b) ∧
        ((promiseSyntax I).cost : ℝ) <
          3000000000000000000000 * p.kappa * (p.signalQubits + 1) * Real.log (1 / p.epsilon) +
          3000000000000000000 * (p.kappa / solutionScale p.alpha A b) * (dataQubits d + 1) ∧
        (2 : ℝ) / 3 < (promiseExecution I).successProbability UA Ub
          (basis (AdaptedExecution.initialIndex p.signalQubits (dataQubits d) (preparationExponent (2 * p.kappa)))) ∧
        ∃ x : PhysicalSource d, ‖x‖ = 1 ∧
          ‖x - physicalSolution A b‖ ≤ p.epsilon + 2 * p.kappa * δ / p.alpha ∧
          (promiseExecution I).conditionalOutput UA Ub
            (basis (AdaptedExecution.initialIndex p.signalQubits (dataQubits d) (preparationExponent (2 * p.kappa)))) =
            pureDensity (WithLp.ofLp x)
end Robust

end Verification.Specification
