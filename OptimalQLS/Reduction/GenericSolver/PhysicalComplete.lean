import OptimalQLS.Reduction.GenericSolver.PhysicalProvenance

/-! All-input and mixed-state soundness of the generic physical substitution. -/
noncomputable section
open scoped Classical
namespace OptimalQLS.Reduction.GenericSolver.Physical
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla LowerBounds
open Refinement.CostedExecution
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
variable {P W : Type} [Fintype P] [DecidableEq P]
  {chart : P ≃ (W → Bool)} {a n : ℕ}

theorem sandwich_of_intertwines {Q : Type} [Fintype Q] [DecidableEq Q]
    (U : Matrix Q Q ℂ) (V : Matrix P P ℂ) (B : Matrix Q P ℂ)
    (h : U*B=B*V) (X : Matrix P P ℂ) :
    U*(B*X*Bᴴ)*Uᴴ=B*(V*X*Vᴴ)*Bᴴ := by
  have hc : Bᴴ*Uᴴ=Vᴴ*Bᴴ := by
    simpa only [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose h
  calc
    _ = (U*B)*X*(Bᴴ*Uᴴ) := by simp only [Matrix.mul_assoc]
    _ = (B*V)*X*(Vᴴ*Bᴴ) := by rw [h,hc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem instructionCode_mixed (i : SourceInstruction chart a n)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (X : Matrix P P ℂ) :
    let U := (((instructionCode i).toQuery gateEval).eval UA Ub).val
    let V := ((i.sourceQuery.toQuery TransducerCompiler.Physical.LocalGate.eval).eval
      (dilationEncoding UA) (preparation Ub)).val
    let B := basisInsertion (clean (P := P))
    U*(B*X*Bᴴ)*Uᴴ=B*(V*X*Vᴴ)*Bᴴ :=
  sandwich_of_intertwines _ _ _ (instructionCode_intertwines i UA Ub) X

/-- This holds for all complex matrices, in particular arbitrary mixed input
densities and states entangled with spectator registers. -/
theorem substitute_mixed (c : SourceCircuit chart a n)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (X : Matrix P P ℂ) :
    let U := (((substitute c).toQuery gateEval).eval UA Ub).val
    let V := (((sourceCircuit c).toQuery TransducerCompiler.Physical.LocalGate.eval).eval
      (dilationEncoding UA) (preparation Ub)).val
    let B := basisInsertion (clean (P := P))
    U*(B*X*Bᴴ)*Uᴴ=B*(V*X*Vᴴ)*Bᴴ :=
  sandwich_of_intertwines _ _ _ (substitute_intertwines c UA Ub) X

/-- Complete coherent refinement remains true with an arbitrary untouched reference. -/
theorem substitute_tensor {R : Type} [Fintype R] [DecidableEq R]
    (c : SourceCircuit chart a n)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    let U := ((substitute c).toQuery gateEval).eval UA Ub
    let V := ((sourceCircuit c).toQuery TransducerCompiler.Physical.LocalGate.eval).eval
      (dilationEncoding UA) (preparation Ub)
    (GateSynthesis.placeHom (Equiv.refl ((P × PhaseScratch) × R)) U).val *
      basisInsertion (fun x : P × R => (clean x.1,x.2)) =
      basisInsertion (fun x : P × R => (clean x.1,x.2)) *
        (GateSynthesis.placeHom (Equiv.refl (P × R)) V).val :=
  tensor_intertwines clean _ _ (substitute_intertwines c UA Ub)

theorem substitute_gate_local (c : SourceCircuit chart a n) (g : Gate chart a n)
    (_hg : NamedInstruction.gate g∈substitute c) :
    IsTwoLocal (coordinates chart) (gateEval g) := gate_local g

end OptimalQLS.Reduction.GenericSolver.Physical
