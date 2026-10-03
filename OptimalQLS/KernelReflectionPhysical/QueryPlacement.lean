import OptimalQLS.KernelReflectionPhysical.Locality
import OptimalQLS.Refinement.CostedExecution.AdapterQueryLocalityFilterDirectCore

/-! # The literal single flag and every original signal/data argument bit -/
noncomputable section
namespace OptimalQLS.KernelReflectionPhysical
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
open Preparation.WorkGates Refinement.CostedExecution Refinement.PhysicalMeasurement
open Reduction.PhysicalAdapter
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
set_option linter.unusedSimpArgs false

def queryControlFrame (a n : ℕ) : ControlFrame (singleFlagPort (D := Bits n) a) :=
  ControlFrame.direct_lift (singleFlagFrame (A := Bits a × Bits n) (smallTarget 2))
    (queryFrame a (Bits n))

def oracleWire (a n : ℕ) : Unit ⊕ (Fin a ⊕ Fin n) →
    (Unit ⊕ Wire (LogicalWire a)) ⊕ Fin n
  | .inl _ => .inl (.inr (.inr 0))
  | .inr (.inl i) => .inl (.inr (.inl (.inr (.inl i))))
  | .inr (.inr i) => .inr i

macro "kernel_query_wire" : tactic => `(tactic| simp [physicalBits,phaseBits,
  queryControlFrame,ControlFrame.direct_lift,singleFlagFrame,flagFrame,
  tensorFrame,queryFrame,Preparation.CompilerAttachment.scratchFrame,
  querySourceFrame,registerEquiv,logicalEquiv,oracleLocalWiring,oracleWire,
  Equiv.funSplitAt_symm_apply,smallTarget,productBits,boolCoordinates,matrixArguments])

def oracleEmbedding (a n : ℕ) :
    WireEmbedding (productBits boolCoordinates (matrixArguments a n))
      (physicalBits (a := a) (fun d : Bits n => d)) (queryControlFrame a n).wiring := by
  letI : Nonempty (queryControlFrame a n).Rest := ⟨((false,fun _=>false),(false,false))⟩
  exact WireEmbedding.ofWireMap (productBits boolCoordinates (matrixArguments a n))
    (physicalBits (a := a) (fun d : Bits n => d)) (queryControlFrame a n).wiring
    (oracleWire a n)
    (by
      intro x r i
      rcases i with i|(i|i)
      · cases i; kernel_query_wire
      · kernel_query_wire
      · rfl)
    (by
      intro x y r j hj
      rcases j with (j|(j|j))|j
      · rfl
      · rcases j with j|(j|j)
        · fin_cases j <;> kernel_query_wire
        · exact False.elim (hj (.inr (.inl j)) rfl)
        · rfl
      · fin_cases j
        · exact False.elim (hj (.inl ()) rfl)
        · kernel_query_wire
      · exact False.elim (hj (.inr (.inr j)) rfl))

/-- A genuine one-flag-controlled invocation of arbitrary UH, with literal
signal/data argument wires and all other physical bits as tensor spectators. -/
def originalOraclePlacement (a n : ℕ) :
    LiteralQueryPlacement (matrixArguments a n)
      (physicalBits (a := a) (fun d : Bits n => d)) (singleFlagPort a) where
  frame := queryControlFrame a n
  wires := oracleEmbedding a n

end OptimalQLS.KernelReflectionPhysical
