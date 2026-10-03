import OptimalQLS.Reduction.DirectMeasurement
import OptimalQLS.Refinement.CostedExecution.AdapterLocality

/-! # Identical physical wires for the gates and the joint head measurement -/
noncomputable section
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
open scoped Classical
namespace OptimalQLS.Reduction.DirectMeasurement
open Matrix TransducerCompiler BinaryClock PolynomialTransform PhysicalPadding
open Refinement CostedExecution

def wireEquiv (a n ℓ : ℕ) : AdapterWire a n ℓ ≃ (AuxWire a ℓ ⊕ Fin n) where
  toFun
    | .inl (.inl i) => .inl (.inl (.inl i))
    | .inl (.inr i) => Fin.cases (.inl (.inr ())) (fun j=>.inr j) i
    | .inr i => .inl (.inl (.inr i))
  invFun
    | .inl (.inl (.inl i)) => .inl (.inl i)
    | .inl (.inl (.inr i)) => .inr i
    | .inl (.inr _) => .inl (.inr 0)
    | .inr i => .inl (.inr i.succ)
  left_inv i := by
    rcases i with (i|i)|i
    · rfl
    · refine Fin.cases ?_ (fun j=>?_) i <;> rfl
    · rfl
  right_inv i := by
    rcases i with ((i|i)|i)|i
    · rfl
    · rfl
    · cases i; rfl
    · rfl

theorem wireEquiv_read (a n ℓ : ℕ) (x : PhysicalAdapter.Space a n ℓ)
    (i : AdapterWire a n ℓ) :
    (registerCoordinates a n ℓ).symm x (wireEquiv a n ℓ i)=adapterCoordinates a n ℓ x i := by
  rcases i with (i|i)|i
  · rfl
  · refine Fin.cases ?_ (fun j=>?_) i <;> rfl
  · rfl

theorem gate_local (a n ℓ : ℕ) (hℓ : 0<ℓ) (g : PhysicalAdapter.Gate a n ℓ) :
    IsTwoLocal (registerCoordinates a n ℓ).symm (PhysicalAdapter.gateEval a n ℓ hℓ g) :=
  IsTwoLocal.wire_equiv (wireEquiv a n ℓ) (wireEquiv_read a n ℓ)
    (adapter_gate_local a n ℓ hℓ g)

end OptimalQLS.Reduction.DirectMeasurement
