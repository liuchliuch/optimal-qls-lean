import OptimalQLS.Preparation.CompilerAttachment.GraphGates
import OptimalQLS.Preparation.BasisInput

/-! # One actual X gate initializes the known graph label -/
noncomputable section
namespace OptimalQLS.Preparation.CompilerAttachment
open Matrix TransducerCompiler BinaryClock PolynomialTransform DirtyAncilla
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

def allZero (a n ℓ : ℕ) : Physical a n ℓ :=
  ((false,(((false,(GraphEncoding.physicalSignalZero (fun _ : Fin a=>false),
    ((0 : Fin 4),(fun _ : Fin n=>false)))),.pub),((fun _=>false),(fun _=>false)))),
    (false,false,false))

def initializeGraphGate : PhaseGate GraphLocalWire :=
  .real (.x (GraphEncoding.coreWire (some 3)))

def initializeGraphCircuit (a n ℓ : ℕ) :
    NamedCircuit (PhaseGate GraphLocalWire) (Bits a × Bits n) (Bits n) (Physical a n ℓ) :=
  [.gate initializeGraphGate]

theorem initializeGraphGate_arity : initializeGraphGate.arity=1 := rfl

theorem initializeGraphGate_real : GraphEncoding.RealPhaseGate initializeGraphGate := by
  change ∀ i j, ((GateSynthesis.LowerGate.x (GraphEncoding.coreWire (some 3))).eval.val i j).im=0
  exact GateSynthesis.LowerGate.eval_real _

theorem initializeGraphCircuit_counts (a n ℓ : ℕ) :
    ((initializeGraphCircuit a n ℓ).toQuery (graphGateEval a n ℓ)).matrixQueries=0 ∧
    ((initializeGraphCircuit a n ℓ).toQuery (graphGateEval a n ℓ)).vectorQueries=0 ∧
    (initializeGraphCircuit a n ℓ).workGates=1 := by
  exact ⟨rfl,rfl,rfl⟩

theorem initializeGraphGate_basis (a n ℓ : ℕ) :
    (graphGateEval a n ℓ initializeGraphGate).val*ᵥPi.single (allZero a n ℓ) 1=
      Pi.single (clean a n ℓ (preparationBasisIndex (fun _ : Fin a=>false)
        (fun _ : Fin n=>false) ℓ)) 1 := by
  let x : GraphLocalWire → Bool := fun _=>false
  let y := (BinaryClock.Gate.x (GraphEncoding.coreWire (some 3))).act x
  let sd : Bits a × Bits n := ((fun _=>false),(fun _=>false))
  let rest : CompilerRest ℓ := (false,false,(fun _=>false),(fun _=>false))
  have hx : graphFrame a n ℓ (((false,x),sd),rest)=allZero a n ℓ := rfl
  have hy : graphFrame a n ℓ (((false,y),sd),rest)=
      clean a n ℓ (preparationBasisIndex (fun _ : Fin a=>false) (fun _ : Fin n=>false) ℓ) := by
    simp [graphFrame,graphLocalWiring,scratchFrame,labelDataFrame,y,x,sd,rest,
      BinaryClock.Gate.act,GraphEncoding.coreWire,Function.update_apply,
      GraphEncoding.graphBits,clean,preparationBasisIndex,GraphEncoding.physicalSignalZero,
      GraphEncoding.signalZero,labelBitsEquiv,labelCode]
  have hlocal := GateSynthesis.lower_x_basis (GraphEncoding.coreWire (some 3)) x
  have hplaced := GateSynthesis.placeHom_basis (Equiv.refl (GraphLocalState × (Bits a × Bits n)))
    initializeGraphGate.eval (false,x) (false,y) sd hlocal
  have hfull := GateSynthesis.placeHom_basis (graphFrame a n ℓ)
    (elementaryPlacement initializeGraphGate.eval) ((false,x),sd) ((false,y),sd) rest hplaced
  rw [hx,hy] at hfull
  exact hfull

theorem initializeGraphCircuit_state (a n : ℕ) {κ s ŝ : ℝ} (h : BudgetParameters κ s ŝ)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ) :
    (((initializeGraphCircuit a n (preparationExponent κ)).toQuery
      (graphGateEval a n (preparationExponent κ))).eval UA Ub).val*ᵥ
      Pi.single (allZero a n (preparationExponent κ)) 1=
    basisInsertion (clean a n (preparationExponent κ))*ᵥ
      preparationBasisInput (fun _ : Fin a=>false) (fun _ : Fin n=>false) h := by
  rw [preparationBasisInput_single,basisInsertion_basis]
  simpa [initializeGraphCircuit,NamedCircuit.toQuery,NamedInstruction.toQuery,
    QueryCircuit.eval,QueryInstruction.eval] using initializeGraphGate_basis a n (preparationExponent κ)

end OptimalQLS.Preparation.CompilerAttachment
