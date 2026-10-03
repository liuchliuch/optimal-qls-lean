import OptimalQLS.TransducerCompiler.Physical.Queries
import OptimalQLS.Refinement.CostedExecution.AdapterQueryLocalityFilterDirectCore

/-! Every generic compiler query acts on the literal original data wires and one flag. -/
noncomputable section
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
open scoped Classical
namespace OptimalQLS.TransducerCompiler.Physical
open Matrix BinaryClock PolynomialTransform DirtyAncilla
open Refinement.CostedExecution Refinement.PhysicalMeasurement
open Preparation.CompilerAttachment Reduction.PhysicalAdapter

abbrev QueryWire (m : ℕ) := (Unit ⊕ OracleLocalWire) ⊕ Fin m

def queryCoordinates (m : ℕ) : OracleLocalState × Bits m ≃ (QueryWire m → Bool) :=
  productBits (phaseCoordinates _) (Equiv.refl _)

def queryWire (m ℓ : ℕ) : QueryWire m → Wire m ℓ
  | .inl (.inl _) => .inr (.inl ())
  | .inl (.inr (.inl i)) => .inl (.inr (.inl (.inr (labelIndex i))))
  | .inl (.inr (.inr i)) => .inr (.inr (labelIndex i))
  | .inr i => .inl (.inr (.inl (.inl i)))

def queryEmbedding (m ℓ : ℕ) :
    WireEmbedding (queryCoordinates m) (coordinates m ℓ) (queryFrame m ℓ) :=
  WireEmbedding.ofWireMap (queryCoordinates m) (coordinates m ℓ) (queryFrame m ℓ)
    (queryWire m ℓ)
    (by
      intro x r i
      rcases i with (i|(i|i))|i
      · cases i; rfl
      · fin_cases i
        · change (labelBitsEquiv (labelBitsEquiv.symm (x.1.2 (.inl 0),x.1.2 (.inl 1)))).1=x.1.2 (.inl 0)
          rw [Equiv.apply_symm_apply]
        · change (labelBitsEquiv (labelBitsEquiv.symm (x.1.2 (.inl 0),x.1.2 (.inl 1)))).2=x.1.2 (.inl 1)
          rw [Equiv.apply_symm_apply]
      · fin_cases i <;> rfl
      · rfl)
    (by
      intro x y r j hj
      rcases j with (j|((j|j)|j))|j
      · rfl
      · exact False.elim (hj (.inr j) rfl)
      · have he : queryWire m ℓ (.inl (.inr (.inl (labelIndex.symm j))))=
            .inl (.inr (.inl (.inr j))) := by simp [queryWire]
        exact False.elim (hj _ he)
      · rfl
      · rcases j with j|j
        · cases j; exact False.elim (hj (.inl (.inl ())) rfl)
        · have he : queryWire m ℓ (.inl (.inr (.inr (labelIndex.symm j))))=.inr (.inr j) := by
            simp [queryWire]
          exact False.elim (hj _ he))

def phaseQueryEmbedding (m : ℕ) : WireEmbedding phaseBits (queryCoordinates m)
    (Equiv.refl (OracleLocalState × Bits m)) where
  wire := Function.Embedding.inl
  read := by intros; rfl
  outside := by
    intro x y r j hj
    cases j with
    | inl j => exact False.elim (hj j rfl)
    | inr j => rfl

theorem query_gate_local (m ℓ : ℕ) (g : PhaseGate OracleLocalWire) :
    IsTwoLocal (coordinates m ℓ) (queryGateEval m ℓ g) :=
  IsTwoLocal.place _ (queryEmbedding m ℓ) _
    (IsTwoLocal.place _ (phaseQueryEmbedding m) _ (phase_leaf_local g))

def singleFlagPort (m ℓ : ℕ) : QueryPort (Bits m) (Space m ℓ) :=
  (scratchPort (queryFrame m ℓ)).comp (GraphEncoding.singleFlagOraclePort (Bits m) (smallTarget 2))

def localFlagEmbedding (m : ℕ) :
    WireEmbedding (productBits boolCoordinates (Equiv.refl (Bits m))) (queryCoordinates m)
      (flagFrame (smallTarget 2) (Bits m)) where
  wire := ⟨fun i=>match i with
    | .inl _ => .inl (.inr (smallTarget 2))
    | .inr i => .inr i,by intro i j he; cases i <;> cases j <;> simp_all⟩
  read := by
    intro x r i
    cases i with
    | inl i => cases i; simp [flagFrame,queryCoordinates,phaseCoordinates,productBits,
        boolCoordinates,Equiv.funSplitAt_symm_apply]
    | inr i => rfl
  outside := by
    intro x y r j hj
    rcases j with (j|j)|j
    · rfl
    · have hn : j≠smallTarget 2 := by intro he; subst j; exact hj (.inl ()) rfl
      simp [flagFrame,queryCoordinates,phaseCoordinates,productBits,Equiv.funSplitAt_symm_apply,hn]
    · exact False.elim (hj (.inr j) rfl)

def queryPlacement (m ℓ : ℕ) :
    LiteralQueryPlacement (Equiv.refl (Bits m)) (coordinates m ℓ) (singleFlagPort m ℓ) where
  frame := Refinement.CostedExecution.ControlFrame.direct_lift
    (singleFlagFrame (A := Bits m) (smallTarget 2)) (queryFrame m ℓ)
  wires := (localFlagEmbedding m).comp (queryEmbedding m ℓ)

end OptimalQLS.TransducerCompiler.Physical
