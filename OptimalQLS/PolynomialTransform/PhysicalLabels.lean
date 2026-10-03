import OptimalQLS.PolynomialTransform.PhysicalPhases

/-! # Constant-size synthesis on the two actual QSVT label wires -/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Matrix DirtyAncilla OptimalQLS.TransducerCompiler
variable {D : Type*} [Fintype D] [DecidableEq D]

theorem average_ne_dilation (a : ℕ) : averageWire a ≠ dilationWire a := by
  simp [averageWire,dilationWire]

def labelRest (a : ℕ) (x : Fin a → Bool) :
    Bool × ({i : QSVTWire a // i ≠ averageWire a ∧ i ≠ dilationWire a} → Bool) :=
  (false,fun i => match i.val with | .inl j => x j | .inr _ => false)

theorem label_clean_wiring (a : ℕ) (k : Bool × Bool) (x : Fin a → Bool) :
    physicalCleanSignal a (k,x)=
      pairWiring (averageWire a) (dilationWire a) (average_ne_dilation a) (k,labelRest a x) := by
  apply Prod.ext
  · rfl
  · funext i
    cases i with
    | inl i => simp [physicalCleanSignal,physicalSignalEquiv,pairWiring,labelRest,averageWire,dilationWire]
    | inr i => fin_cases i <;>
        simp [physicalCleanSignal,physicalSignalEquiv,pairWiring,labelRest,averageWire,dilationWire]

/-- Any unitary on the two labels is one actual two-qubit instruction. -/
def physicalLabelCode (a : ℕ) (U : Matrix.unitaryGroup (Bool × Bool) ℂ) :
    List (PhaseGate (QSVTWire a)) :=
  [.pair (averageWire a) (dilationWire a) (average_ne_dilation a) U]

def logicalLabels (a : ℕ) (U : Matrix.unitaryGroup (Bool × Bool) ℂ) :
    Matrix.unitaryGroup (LogicalSignal a × D) ℂ :=
  GateSynthesis.placeHom (Equiv.prodAssoc (Bool × Bool) (Fin a → Bool) D).symm U

theorem physicalLabels_intertwines (a : ℕ) (U : Matrix.unitaryGroup (Bool × Bool) ℂ) :
    (elementaryPlacement (D := D) (phaseEval (physicalLabelCode a U))).val *
      basisInsertion (physicalClean a)=
      basisInsertion (physicalClean a)*(logicalLabels (D := D) a U).val := by
  have h := placeHom_natural (Equiv.refl ((Bool × Bool) × (Fin a → Bool)))
    (pairWiring (averageWire a) (dilationWire a) (average_ne_dilation a))
    (physicalCleanSignal a) (labelRest a) (label_clean_wiring a) U
  have ht := tensor_intertwines (D := D) (physicalCleanSignal a)
    (GateSynthesis.placeHom (pairWiring (averageWire a) (dilationWire a) (average_ne_dilation a)) U)
    (GateSynthesis.placeHom (Equiv.refl ((Bool × Bool) × (Fin a → Bool))) U) h
  simpa only [physicalLabelCode,phaseEval,PhaseGate.eval,one_mul,elementaryPlacement,
    physicalClean,placeHom_tensor_assoc,logicalLabels] using ht

theorem logicalLabels_synthesis (a : ℕ) (U : Matrix.unitaryGroup (Bool × Bool) ℂ) :
    ∃ code : List (PhaseGate (QSVTWire a)), code.length ≤ 781*(a+1) ∧
      (elementaryPlacement (D := D) (phaseEval code)).val*basisInsertion (physicalClean a)=
        basisInsertion (physicalClean a)*(logicalLabels (D := D) a U).val := by
  refine ⟨physicalLabelCode a U,?_,physicalLabels_intertwines a U⟩
  simp [physicalLabelCode]
  omega

end OptimalQLS.PolynomialTransform
