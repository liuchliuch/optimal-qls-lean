import OptimalQLS.PhysicalRobustness.GeneralProgram.Resources
import OptimalQLS.OracleCoordinateResources

/-! Resource attachment on all actual terminal paths and oracle coordinate changes. -/
noncomputable section
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
open scoped Classical
namespace OptimalQLS.PhysicalRobustness.GeneralProgram
open Matrix LowerBounds PhysicalPadding Reduction TransducerCompiler BinaryClock PolynomialTransform
open Refinement Refinement.PhysicalExecution Refinement.Repetition
variable {a n : ℕ} {κ ŝ ε : ℝ}

theorem physicalExecution_instrument_depth (I : Implementation a n κ ŝ ε) :
    instrumentDepth (physicalExecution I)=(physicalSyntax I).cost+1 :=
  DirectCosted.instrument_depth _ _ _

/-- Every terminal, including zero-weight and failure terminals, has the
separately proved worst-case oracle bounds. -/
theorem physicalExecution_terminal_queries_le (I : Implementation a n κ ŝ ε)
    (v : Fin (Fintype.card (PhysicalAdapter.Space a n (preparationExponent (2*κ)))) → ℂ)
    (k : (physicalExecution I).Terminal) :
    ((physicalExecution I).terminalPath (.initial v) k).matrixQueries≤1200000*I.runCircuit.matrixQueries ∧
    ((physicalExecution I).terminalPath (.initial v) k).vectorQueries≤600000*I.runCircuit.vectorQueries := by
  constructor
  · simpa only [VariableQueryPath.matrixQueries,zero_add,(physicalExecution_query_depths I).1]
      using terminalPath_matrixQueries_le (physicalExecution I) (.initial v) k
  · simpa only [VariableQueryPath.vectorQueries,zero_add,(physicalExecution_query_depths I).2]
      using terminalPath_vectorQueries_le (physicalExecution I) (.initial v) k

/-- This is the actual named/measurement/X path, projected from the lowered
execution, rather than an unrelated numeric elementary-work budget. -/
theorem physicalExecution_terminalCost_le (I : Implementation a n κ ŝ ε)
    (k : (physicalExecution I).Terminal) :
    (physicalSyntax I).terminalCost
      ((physicalSyntax I).projectTerminal
        (DirectMeasurement.finiteCoordinates a n (preparationExponent (2*κ)))
        (HadamardClock.bitsFinEquiv n)
        (DirectCosted.finiteGate a n (preparationExponent (2*κ))
          (Preparation.CompilerAttachment.preparationExponent_pos I.budget)) k)≤(physicalSyntax I).cost :=
  CostedExecution.Program.lowered_terminalCost_le _ _ _ _ _

end OptimalQLS.PhysicalRobustness.GeneralProgram
