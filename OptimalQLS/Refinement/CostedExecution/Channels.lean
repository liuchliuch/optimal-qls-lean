import OptimalQLS.Refinement.CostedExecution.Attachment

/-! Mixed-state refinement of the same normalized output channels. -/
noncomputable section
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace OptimalQLS.Refinement.CostedExecution
open Matrix LowerBounds
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

section Channels
variable {D O : Type*} [Fintype D] [DecidableEq D] [Fintype O] [DecidableEq O]

theorem sum_column_pureDensity (M : Matrix D D ℂ) :
    (∑ j : D, pureDensity (fun i=>M i j))=M*M.conjTranspose := by
  ext i j
  simp [Matrix.sum_apply,pureDensity,ketBra,Matrix.vecMulVec,Matrix.mul_apply,Matrix.conjTranspose_apply]

theorem channel_apply_sum (Φ : FiniteChannel D O) {I : Type*} [Fintype I]
    (X : I → Matrix D D ℂ) : Φ.apply (∑ i,X i)=∑ i,Φ.apply (X i) := by
  simp only [FiniteChannel.apply,Matrix.mul_sum,Matrix.sum_mul]
  rw [Finset.sum_comm]

/-- Pure-vector equality extends to every positive density matrix, normalized
or not. This conclusion does not assume a channel-realization certificate. -/
theorem channel_eq_of_pure (Φ Ψ : FiniteChannel D O)
    (hp : ∀ v : D → ℂ, Φ.apply (pureDensity v)=Ψ.apply (pureDensity v))
    (X : Matrix D D ℂ) (hX : X.PosSemidef) : Φ.apply X=Ψ.apply X := by
  have hs : (CFC.sqrt X).conjTranspose=CFC.sqrt X :=
    (show (CFC.sqrt X).PosSemidef from (CFC.sqrt_nonneg X).posSemidef).isHermitian.eq
  have hx : (∑ j : D,pureDensity (fun i=>(CFC.sqrt X) i j))=X := by
    rw [sum_column_pureDensity,hs,CFC.sqrt_mul_sqrt_self X hX.nonneg]
  rw [← hx,channel_apply_sum,channel_apply_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact hp _
end Channels

variable {G A B Aux Data : Type*} [Fintype Aux] [DecidableEq Aux]
  [Fintype Data] [DecidableEq Data] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  {d w : ℕ}

/-- The expanded syntax and existing repeat program agree on arbitrary mixed
input states too, with success/failure retained in the two output sectors. -/
theorem repeated_channel_refines (E : State Aux Data ≃ Fin w) (F : (Data → Bool) ≃ Fin d)
    (gate : G → Matrix.unitaryGroup (Fin w) ℂ)
    (c : PolynomialTransform.NamedCircuit G A B (Fin w)) (accepted : Aux → Bool)
    (zero : State Aux Data) (out : Fin d) (R : ℕ)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (X : Matrix (Fin w) (Fin w) ℂ) (hX : X.PosSemidef) :
    (((repeated F c accepted zero out R).lower E F gate).outputChannel UA Ub).apply X =
      ((Repetition.repeatProgram (c.toQuery gate)
        (Repetition.reindexEmbedding E F (Repetition.Physical.auxEmbedding accepted))
        (E zero) out R).outputChannel UA Ub).apply X := by
  apply channel_eq_of_pure _ _ _ X hX
  intro v
  rw [FiniteOracleProgram.outputChannel_pureDensity,FiniteOracleProgram.outputChannel_pureDensity]
  rw [show ((repeated F c accepted zero out R).lower E F gate).executeDensity UA Ub id v = _ from
      repeated_refines E F gate UA Ub id c accepted zero out R v]
  rw [show ((repeated F c accepted zero out R).lower E F gate).executeDensity UA Ub Bool.not v = _ from
      repeated_refines E F gate UA Ub Bool.not c accepted zero out R v]

open Preparation PhysicalPadding TransducerCompiler BinaryClock
variable {a n : ℕ} {κ s ŝ ε : ℝ} {h : BudgetParameters κ s ŝ}
attribute [local irreducible] Repetition.repeatProgram repeated Program.lower

theorem execution_channel_refines (I : PhysicalProgram.Implementation a n (ε:=ε) h)
    (UA : Matrix.unitaryGroup (Bits a × Bits n) ℂ) (Ub : Matrix.unitaryGroup (Bits n) ℂ)
    (X : Matrix (Fin (Fintype.card (PhysicalProgram.Register a n (preparationExponent κ))))
      (Fin (Fintype.card (PhysicalProgram.Register a n (preparationExponent κ)))) ℂ) (hX : X.PosSemidef) :
    ((physicalLower I 72000).outputChannel UA Ub).apply X =
      ((PhysicalExecution.execution I).outputChannel UA Ub).apply X := by
  apply channel_eq_of_pure _ _ _ X hX
  intro v
  rw [FiniteOracleProgram.outputChannel_pureDensity,FiniteOracleProgram.outputChannel_pureDensity]
  rw [execution_refines I UA Ub id v,execution_refines I UA Ub Bool.not v]

end OptimalQLS.Refinement.CostedExecution
