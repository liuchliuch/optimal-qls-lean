import OptimalQLS.Reduction.GenericSolver.FreshCopiesProcess
import OptimalQLS.Refinement.Repetition.Resources

/-! Exact oracle depths and live-register bounds of the physical fresh-copy
tree. Literal partial traces can only remove physical wires. -/
noncomputable section
open scoped Classical
namespace OptimalQLS.Reduction.GenericSolver.FreshCopies
open Matrix LowerBounds Refinement.CostedExecution
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

theorem TensorLayout.rest_nonempty {R Q : Register} (F : TensorLayout R.bits Q.bits) :
    Nonempty F.Rest :=
  ⟨(F.frame.symm (R.bits.symm (fun _ => false))).2⟩

/-- The surviving output wires are distinct literal input wires. -/
theorem TensorLayout.output_qubits_le {R Q : Register} (F : TensorLayout R.bits Q.bits) :
    Q.qubits ≤ R.qubits :=
  Fintype.card_le_of_injective F.wires.wire F.wires.wire.injective

theorem TensorLayout.output_dimension_le {R Q : Register} (F : TensorLayout R.bits Q.bits) :
    Q.dimension ≤ R.dimension := by
  rw [Q.dimension_eq, R.dimension_eq]
  exact pow_le_pow_right' (by decide : (1 : ℕ) ≤ 2) F.output_qubits_le

private theorem sup_two (f : Fin 2 → ℕ) : Finset.univ.sup f = max (f 0) (f 1) := by
  apply le_antisymm
  · apply Finset.sup_le
    intro i _
    fin_cases i
    · exact Nat.le_max_left _ _
    · exact Nat.le_max_right _ _
  · exact max_le (Finset.le_sup (f := f) (Finset.mem_univ 0))
      (Finset.le_sup (f := f) (Finset.mem_univ 1))

private theorem sup_rest_const {R Q : Register} (F : TensorLayout R.bits Q.bits) (n : ℕ) :
    (Finset.univ.sup (fun _ : Fin (Fintype.card F.Rest) => n)) = n := by
  let r := (F.frame.symm (R.bits.symm (fun _ => false))).2
  exact Finset.sup_const ⟨Fintype.equivFin F.Rest r, Finset.mem_univ _⟩ n

namespace Process
variable {A B VA VB : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  {argumentsA : A ≃ (VA → Bool)} {argumentsB : B ≃ (VB → Bool)} {O R : Register}

theorem lower_matrixCalls (p : Process argumentsA argumentsB O R) :
    Refinement.Repetition.matrixDepth p.lower = p.matrixCalls := by
  induction p with
  | unitary U h next ih => simpa [lower, Refinement.Repetition.matrixDepth, matrixCalls] using ih
  | matrix port adj L next ih => simp [lower, Refinement.Repetition.matrixDepth, matrixCalls, ih]
  | vector port adj L next ih => exact ih
  | measure i next ih =>
    simp only [lower, Refinement.Repetition.matrixDepth, ih, sup_two, matrixCalls]
    rfl
  | trace F next ih =>
    simp only [lower, Refinement.Repetition.matrixDepth, ih, matrixCalls]
    exact sup_rest_const F _
  | output flag => rfl

theorem lower_vectorCalls (p : Process argumentsA argumentsB O R) :
    p.lower.vectorDepth = p.vectorCalls := by
  induction p with
  | unitary U h next ih => simpa [lower, FiniteOracleProgram.vectorDepth, vectorCalls] using ih
  | matrix port adj L next ih => exact ih
  | vector port adj L next ih => simp [lower, FiniteOracleProgram.vectorDepth, vectorCalls, ih]
  | measure i next ih =>
    simp only [lower, FiniteOracleProgram.vectorDepth, ih, sup_two, vectorCalls]
    rfl
  | trace F next ih =>
    simp only [lower, FiniteOracleProgram.vectorDepth, ih, vectorCalls]
    exact sup_rest_const F _
  | output flag => rfl

theorem lower_registerBound_le (p : Process argumentsA argumentsB O R)
    {M : ℕ} (h : R.dimension ≤ M) : Refinement.Repetition.RegisterBound M p.lower := by
  induction p generalizing M with
  | unitary U hl next ih => exact ⟨h, fun _ => ih h⟩
  | matrix port adj L next ih => exact ⟨h, ih h⟩
  | vector port adj L next ih => exact ⟨h, ih h⟩
  | measure i next ih => exact ⟨h, fun b => ih (outcome b) h⟩
  | trace F next ih => exact ⟨h, fun _ => ih (F.output_dimension_le.trans h)⟩
  | output flag => exact h

/-- All fresh copies are already present in the input. Neither branching nor
discard retains a coherent history or allocates a larger live register. -/
theorem lower_registerBound (p : Process argumentsA argumentsB O R) :
    Refinement.Repetition.RegisterBound R.dimension p.lower := p.lower_registerBound_le le_rfl

theorem lower_qubitBound (p : Process argumentsA argumentsB O R) :
    Refinement.Repetition.RegisterBound (2 ^ R.qubits) p.lower := by
  rw [← R.dimension_eq]
  exact p.lower_registerBound

end Process
end OptimalQLS.Reduction.GenericSolver.FreshCopies
