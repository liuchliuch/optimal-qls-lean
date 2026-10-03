import OptimalQLS.GraphEncoding.Proposition43
import OptimalQLS.GraphEncoding.SingleFlagTheorem

/-! Proposition 4.3, with encoding and every allowed-call implementation
referring to the same globally Hermitian graph oracle. -/
noncomputable section
namespace OptimalQLS.PaperStatements
open Matrix PolynomialTransform GraphEncoding DirtyAncilla
set_option synthInstance.maxSize 4096
variable {S D B : Type*} [Fintype S] [DecidableEq S]
  [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

/-- The circuit and controlled-call words precede the complete input oracles. -/
theorem proposition43 [Nonempty D] (κ : ℝ) (hκ : 2 ≤ κ) (s₀ : S) :
    let hp : 0 < κ := by linarith
    let c := elementaryGraphCircuit S D B κ hp
    c.matrixQueries = 2 ∧ c.vectorQueries = 0 ∧ workInstructions c = 76 ∧
    (∀ a, Fintype.card S = 2^a → Fintype.card (GraphEncoding.PhysicalSignal S) = 2^(a+4)) ∧
    (∀ (UA : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ)
      (A : Matrix D D ℂ), A.IsHermitian → IsBlockEncoding s₀ 1 0 UA A →
      c.eval UA Ub = physicalEncoding κ hp UA ∧
      (c.eval UA Ub).val.IsHermitian ∧
      IsBlockEncoding (physicalSignalZero s₀) (1+κ⁻¹) 0 (c.eval UA Ub) (graphMatrix A κ)) ∧
    (∀ mask : Bool × Bool,
      ∃ call : ElementaryCircuit (S × D) B ControlledGraphWire (S × D),
        call.toQuery.matrixQueries = 2 ∧ call.toQuery.vectorQueries = 0 ∧
        call.workGates ≤ 252304 ∧ SingleFlagRealCircuit GraphEncoding.flagWire call ∧
        ∀ (adj : Bool) (UA : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ),
          (call.toQuery.eval UA Ub).val * basisInsertion (graphLocalClean (S := S) (D := D)) =
            basisInsertion (graphLocalClean (S := S) (D := D)) *
              ((maskedGraphPort (GraphEncoding.PhysicalSignal S × (Fin 4 × D)) mask).apply
                (if adj then (c.eval UA Ub)⁻¹ else c.eval UA Ub)).val) := by
  dsimp only
  have hp : 0 < κ := by linarith
  refine ⟨(elementaryGraphCircuit_counts κ hp).1,
    (elementaryGraphCircuit_counts κ hp).2.1,
    (elementaryGraphCircuit_counts κ hp).2.2, physical_signal_qubits, ?_, ?_⟩
  · intro UA Ub A hA henc
    rw [elementaryGraphCircuit_eval]
    exact ⟨rfl, physicalEncoding_hermitian κ hp UA,
      physicalEncoding_exact κ hp s₀ UA A hA henc⟩
  · intro mask
    obtain ⟨call, hm, hb, hg, hs, he⟩ :=
      controlled_graph_single_flag (S := S) (D := D) (B := B) κ hp mask
    refine ⟨call, hm, hb, hg, hs, ?_⟩
    intro adj UA Ub
    simpa only [elementaryGraphCircuit_eval] using he adj UA Ub

end OptimalQLS.PaperStatements
