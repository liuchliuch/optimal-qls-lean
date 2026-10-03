import OptimalQLS.Reduction.PhysicalUpper
import OptimalQLS.OracleSyntaxCoordinates

/-! The conventional program is the lowering of the same physical bit syntax. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
open scoped Classical
namespace OptimalQLS.Reduction.PhysicalUpper
open Matrix PhysicalPadding TransducerCompiler BinaryClock PolynomialTransform
open Refinement Repetition CostedExecution
variable {p : QLSParameters} {d : ℕ} {hκ : 2≤p.kappa}
attribute [local irreducible] repeated CostedExecution.Program.lower repeatProgram

def promiseSyntax (I : Implementation p d hκ) :=
  (DirectCosted.algorithmSyntax I).mapOracles
    (oracleRegisterCoordinates p.signalQubits d) (physicalDataCoordinates d)

theorem promiseSyntax_lower (I : Implementation p d hκ) :
    (promiseSyntax I).lower
      (DirectMeasurement.finiteCoordinates p.signalQubits (dataQubits d) (preparationExponent p.kappa))
      (HadamardClock.bitsFinEquiv (dataQubits d))
      (DirectCosted.finiteGate p.signalQubits (dataQubits d) (preparationExponent p.kappa)
        (Preparation.CompilerAttachment.preparationExponent_pos (publicBudget p hκ)))=
      promiseExecution I :=
  CostedExecution.Program.mapOracles_lower _ _ _ _ _ _

theorem promiseSyntax_cost (I : Implementation p d hκ) :
    (promiseSyntax I).cost=(DirectCosted.algorithmSyntax I).cost :=
  CostedExecution.Program.mapOracles_cost _ _ _

theorem promise_instrument_depth (I : Implementation p d hκ) :
    instrumentDepth (promiseExecution I)=(promiseSyntax I).cost+1 := by
  rw [promiseExecution,OracleCoordinates.program_instrumentDepth,promiseSyntax_cost]
  exact DirectCosted.instrument_depth _ _ _

theorem promise_terminalCost_le (I : Implementation p d hκ)
    (k : ((promiseSyntax I).lower
      (DirectMeasurement.finiteCoordinates p.signalQubits (dataQubits d) (preparationExponent p.kappa))
      (HadamardClock.bitsFinEquiv (dataQubits d))
      (DirectCosted.finiteGate p.signalQubits (dataQubits d) (preparationExponent p.kappa)
        (Preparation.CompilerAttachment.preparationExponent_pos (publicBudget p hκ)))).Terminal) :
    (promiseSyntax I).terminalCost ((promiseSyntax I).projectTerminal
      (DirectMeasurement.finiteCoordinates p.signalQubits (dataQubits d) (preparationExponent p.kappa))
      (HadamardClock.bitsFinEquiv (dataQubits d))
      (DirectCosted.finiteGate p.signalQubits (dataQubits d) (preparationExponent p.kappa)
        (Preparation.CompilerAttachment.preparationExponent_pos (publicBudget p hκ))) k)≤
      (promiseSyntax I).cost :=
  CostedExecution.Program.lowered_terminalCost_le _ _ _ _ k

end OptimalQLS.Reduction.PhysicalUpper
