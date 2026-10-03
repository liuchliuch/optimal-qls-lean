import OptimalQLS.PhysicalRobustness.GeneralProgram.Paths
import OptimalQLS.PhysicalRobustness.GeneralProgram.PromiseInputs
import OptimalQLS.Reduction.DirectSafety

/-! Semantic primitive safety on exactly the executed binary and supplied-register trees. -/
noncomputable section
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
open scoped Classical
namespace OptimalQLS.PhysicalRobustness.GeneralProgram
open Matrix LowerBounds PhysicalPadding Reduction TransducerCompiler BinaryClock PolynomialTransform
open Refinement Refinement.PhysicalExecution Refinement.Repetition
variable {a n : ℕ} {κ ŝ ε : ℝ}

/-- Every actual primitive gate is two-local, and every original query has
literal argument/control wires and source-word provenance in the same chart. -/
def PhysicallySafe (I : Implementation a n κ ŝ ε) : Prop :=
  DirectCosted.PhysicalSafety (circuit I)
    (Preparation.CompilerAttachment.preparationExponent_pos I.budget) 600000

theorem physical_safe (I : Implementation a n κ ŝ ε) : PhysicallySafe I :=
  DirectCosted.physicalSyntax_safe (circuit I) _ 600000 (circuit_safe I)

variable {d : ℕ} {p : QLSParameters}

def promiseExecution (I : Implementation p.signalQubits (dataQubits d) p.kappa
    (publicEstimate p.kappa p.normEstimate) p.epsilon) :=
  OracleCoordinates.program (oracleRegisterCoordinates p.signalQubits d) (physicalDataCoordinates d)
    (physicalExecution I)

/-- This is the actual primitive syntax for the conventional supplied oracles. -/
def promiseSyntax (I : Implementation p.signalQubits (dataQubits d) p.kappa
    (publicEstimate p.kappa p.normEstimate) p.epsilon) :=
  DirectCosted.sourceSyntax (circuit I) 600000
    (oracleRegisterCoordinates p.signalQubits d) (physicalDataCoordinates d)

def PromiseSafe (I : Implementation p.signalQubits (dataQubits d) p.kappa
    (publicEstimate p.kappa p.normEstimate) p.epsilon) : Prop :=
  DirectCosted.CoordinateSafety (circuit I)
    (Preparation.CompilerAttachment.preparationExponent_pos I.budget) 600000
    (oracleRegisterCoordinates p.signalQubits d) (physicalDataCoordinates d)

theorem promise_safe (I : Implementation p.signalQubits (dataQubits d) p.kappa
    (publicEstimate p.kappa p.normEstimate) p.epsilon) : PromiseSafe I :=
  DirectCosted.sourceSyntax_safe (circuit I) _ 600000 (circuit_safe I) _ _

theorem promiseSyntax_cost (I : Implementation p.signalQubits (dataQubits d) p.kappa
    (publicEstimate p.kappa p.normEstimate) p.epsilon) :
    (promiseSyntax I).cost=(physicalSyntax I).cost :=
  DirectCosted.sourceSyntax_cost _ _ _ _

/-- An exact syntax/lowering identity attaches both safety and primitive cost
to the very program appearing in the conventional theorem's Born semantics. -/
theorem promiseSyntax_lower (I : Implementation p.signalQubits (dataQubits d) p.kappa
    (publicEstimate p.kappa p.normEstimate) p.epsilon) :
    (promiseSyntax I).lower
      (DirectMeasurement.finiteCoordinates p.signalQubits (dataQubits d) (preparationExponent (2*p.kappa)))
      (HadamardClock.bitsFinEquiv (dataQubits d))
      (DirectCosted.finiteGate p.signalQubits (dataQubits d) (preparationExponent (2*p.kappa))
        (Preparation.CompilerAttachment.preparationExponent_pos I.budget))=promiseExecution I :=
  DirectCosted.sourceSyntax_lower _ _ _ _ _

end OptimalQLS.PhysicalRobustness.GeneralProgram
