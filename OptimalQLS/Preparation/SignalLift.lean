import OptimalQLS.Preparation.Circuit
import OptimalQLS.OracleComposition
import OptimalQLS.InputReflection

noncomputable section
namespace OptimalQLS.Preparation
open Matrix
variable {S D A : Type*} [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]
  [Fintype A] [DecidableEq A]

/-- The data oracle is tensored with an untouched signal register. -/
def signalLift (U : Matrix.unitaryGroup D ℂ) : Matrix.unitaryGroup (S × D) ℂ :=
  rewireUnitary (Equiv.prodComm D S) (TransducerCompiler.controlledOn (fun _ : S => true) U)

/-- The exact wiring of that tensor extension as one query port. -/
def signalLiftPort (S D : Type*) [Fintype S] : QueryPort D (S × D) where
  multiplicity := Fintype.card S
  wiring := (Equiv.prodCongr (Equiv.refl D) (Fintype.equivFin S).symm).trans (Equiv.prodComm D S)
  control _ := true

theorem signalLiftPort_apply (U : Matrix.unitaryGroup D ℂ) :
    (signalLiftPort S D).apply U = signalLift (S := S) U := by
  apply Subtype.ext
  ext ⟨s,i⟩ ⟨t,j⟩
  simp [signalLiftPort,signalLift,QueryPort.apply,rewireUnitary,controlledUnitary,
    TransducerCompiler.controlledOn,Matrix.blockDiagonal_apply,eq_comm]

/-- The entire tensor oracle has the correct action on every signal sector. -/
theorem signalLift_injection (s₀ : S) (U : Matrix.unitaryGroup D ℂ) (x : D → ℂ) :
    (signalLift (S := S) U : Matrix (S × D) (S × D) ℂ)*ᵥ(signalInjection s₀*ᵥx) =
      signalInjection s₀*ᵥ((U : Matrix D D ℂ)*ᵥx) := by
  rw [signalLift,TransducerCompiler.rewire_apply]
  ext ⟨s,i⟩
  change ((TransducerCompiler.controlledOn (fun _ : S => true) U :
    Matrix (D × S) (D × S) ℂ)*ᵥ_) (i,s) = _
  rw [TransducerCompiler.controlledOn_apply]
  by_cases hs : s=s₀
  · simp [hs,Function.comp_def]
  · simp only [Function.comp_apply, Equiv.prodComm_apply, Prod.swap, signalInjection_mulVec,
      if_neg hs, ite_true]
    change ((U : Matrix D D ℂ)*ᵥ(0 : D → ℂ)) i = 0
    rw [Matrix.mulVec_zero]
    rfl

/-- Input reflection on an enlarged public space still uses precisely two
queries to the original full vector-preparation unitary. -/
def inputReflectionOnSignalCircuit (s₀ : S) (d₀ : D) : QueryCircuit A D (S × D) :=
  [.vectorCall (signalLiftPort S D) true,
   .work (basisStateReflection (s₀,d₀)),
   .vectorCall (signalLiftPort S D) false]

theorem inputReflectionOnSignalCircuit_eval (s₀ : S) (d₀ : D)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup D ℂ) :
    (inputReflectionOnSignalCircuit (A := A) s₀ d₀).eval UA Ub =
      preparedReflection (signalLift (S := S) Ub) (s₀,d₀) := by
  simp only [inputReflectionOnSignalCircuit,QueryCircuit.eval,QueryInstruction.eval,
    ite_true,Bool.false_eq_true,ite_false,one_mul,signalLiftPort_apply]
  have hi : signalLift (S := S) Ub⁻¹ = (signalLift (S := S) Ub)⁻¹ := by
    rw [← signalLiftPort_apply,← signalLiftPort_apply,QueryPort.apply_inv]
  rw [hi]
  rfl

theorem inputReflectionOnSignalCircuit_counts (s₀ : S) (d₀ : D) :
    (inputReflectionOnSignalCircuit (A := A) s₀ d₀).matrixQueries=0 ∧
    (inputReflectionOnSignalCircuit (A := A) s₀ d₀).vectorQueries=2 := by
  simp [inputReflectionOnSignalCircuit,QueryCircuit.matrixQueries,QueryCircuit.vectorQueries]

end OptimalQLS.Preparation
