import OptimalQLS.Refinement.Theorem56
import OptimalQLS.Refinement.Repetition.Transport

/-! Proposition 5.6: one oracle-independent refinement circuit with its literal
normalized success instrument, accepted vector, accuracy and separate costs. -/
noncomputable section
namespace OptimalQLS.PaperStatements
open Matrix PolynomialTransform Preparation Refinement Refinement.Repetition
open scoped Matrix.Norms.L2Operator BigOperators
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1000000
variable {P D B : Type*} [Fintype P] [DecidableEq P] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B] [Nonempty D]

/-- The three success registers are tested jointly; the data is extracted
coherently, so no intermediate preparation/filter measurement occurs. -/
def refinementSuccessEmbedding (a : ℕ) (p₀ : P) :
    Fin (Fintype.card D) ↪ Fin (Fintype.card (RunSpace a P D)) :=
  reindexEmbedding (Fintype.equivFin (RunSpace a P D)) (Fintype.equivFin D)
    ⟨fun i => (physicalZero a,(p₀,(physicalZero (a+4),(2,i)))),
      fun _ _ h => congrArg (fun x => x.2.2.2.2) h⟩

/-- This is the exact accepting Kraus action on every possible final vector. -/
theorem refinementSuccess_action (a : ℕ) (p₀ : P) (v : RunSpace a P D → ℂ) :
    acceptMatrix (refinementSuccessEmbedding (D := D) a p₀) *ᵥ
      (v ∘ (Fintype.equivFin (RunSpace a P D)).symm) =
      accepted p₀ (physicalZero (a+4)) (physicalZero a) v ∘ (Fintype.equivFin D).symm := by
  rw [acceptMatrix_mulVec]
  funext i
  simp [refinementSuccessEmbedding, reindexEmbedding, Function.comp_def, accepted]

/- The same code is quantified before all full oracle matrices and every
unit coarse state satisfying the source's exact kernel-component premise. -/
/-- Complete uniform semantic/resource guarantee for one selected circuit. -/
def RefinementGuarantee (a : ℕ) (p₀ : P) (κ ε : ℝ)
    (out : NamedRefinementCircuit a P D B) : Prop :=
      ((out.toQuery (RefinementGate.eval a)).matrixQueries : ℝ) < 840096*κ*Real.log (1/(ε/1024)) ∧
      (out.toQuery (RefinementGate.eval a)).vectorQueries = 0 ∧
      (out.workGates : ℝ) ≤ 3341621776*κ*(a+1)*Real.log (1/(ε/1024)) ∧
      (∀ g, NamedInstruction.gate g ∈ out → g.arity ≤ 2) ∧
      (∀ zero : Fin (Fintype.card (RunSpace a P D)),
        (∑ i, (measurementKraus (refinementSuccessEmbedding (D := D) a p₀) zero i).conjTranspose *
          measurementKraus (refinementSuccessEmbedding (D := D) a p₀) zero i) = 1) ∧
      ∀ (UA : Matrix.unitaryGroup ((Fin a → Bool) × D) ℂ) (Ub : Matrix.unitaryGroup B ℂ)
        (A : Matrix D D ℂ), A.IsHermitian → IsUnit A →
        IsBlockEncoding (fun _ : Fin a => false) 1 0 UA A → ‖Ring.inverse A‖ ≤ κ →
        ∀ (b : EuclideanSpace ℂ D), ‖b‖ = 1 →
        ∀ (Ψ : P × (Fin 4 × D) → ℂ), ‖WithLp.toLp 2 Ψ‖ = 1 →
        (∃ β : ℝ, 1/32 ≤ β ∧ β ≤ 1 ∧
          Alignment.kernelProjector (GraphEncoding.graphMatrix A κ)
            (WithLp.toLp 2 (fun x => Ψ (p₀,x))) =
              β • Alignment.normalizedProjectedInput (GraphEncoding.graphMatrix A κ) (graphInput b)) →
        let v := (((out.toQuery (RefinementGate.eval a)).eval UA Ub).val *ᵥ
          jointInput (physicalZero (a+4)) (physicalZero a) Ψ)
        let z := WithLp.toLp 2 (accepted p₀ (physicalZero (a+4)) (physicalZero a) v)
        let x := NormedSpace.normalize (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (Ring.inverse A) b)
        acceptMatrix (refinementSuccessEmbedding (D := D) a p₀) *ᵥ
          (v ∘ (Fintype.equivFin (RunSpace a P D)).symm) =
          WithLp.ofLp z ∘ (Fintype.equivFin D).symm ∧
        z ≠ 0 ∧ ‖NormedSpace.normalize z-x‖ ≤ ε/2 ∧ 1/65536 < ‖z‖^2 ∧ ‖z‖^2 ≤ 1

theorem proposition56 (a : ℕ) (p₀ : P) {κ ε : ℝ}
    (hκ : 2 ≤ κ) (hε0 : 0 < ε) (hε1 : ε < 1/2) :
    ∃ out : NamedRefinementCircuit a P D B, RefinementGuarantee a p₀ κ ε out := by
  obtain ⟨out, hm, hv, hg, he⟩ := theorem56_coherent_refinement (D := D) (B := B) a p₀ hκ hε0 hε1
  refine ⟨out, hm, hv, hg, (fun g _ => RefinementGate.arity_le_two g), ?_, ?_⟩
  · intro zero
    exact measurementKraus_complete _ zero
  · intro UA Ub A hA hunit henc hinv b hb Ψ hΨ hcoarse
    exact ⟨refinementSuccess_action a p₀ _, he UA Ub A hA hunit henc hinv b hb Ψ hΨ hcoarse⟩

end OptimalQLS.PaperStatements
