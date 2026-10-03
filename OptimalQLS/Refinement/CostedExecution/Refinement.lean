import OptimalQLS.Refinement.CostedExecution.Discard
import OptimalQLS.Refinement.CostedExecution.Repeated

/-! Equality of the actual expanded physical tree with the existing compressed
repeat program, for every input vector and both output flags. -/
noncomputable section
open scoped BigOperators Classical
namespace OptimalQLS.Refinement.CostedExecution
open Matrix LowerBounds Repetition.Physical PolynomialTransform
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
variable {G A B Aux Data : Type*} [Fintype Aux] [DecidableEq Aux]
  [Fintype Data] [DecidableEq Data] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  {d w : ℕ}
variable (E : State Aux Data ≃ Fin w) (F : (Data → Bool) ≃ Fin d)
  (gate : G → Matrix.unitaryGroup (Fin w) ℂ)
  (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (select : Bool → Bool)

theorem masked_split (a : Aux → Bool) (b : Data → Bool) (v : Fin w → ℂ) :
    masked E Sum.inr b (masked E Sum.inl a v) = masked E id (Sum.elim a b) v := by
  ext j
  simp only [masked,Sum.forall,id_eq,Sum.elim_inl,Sum.elim_inr]
  split_ifs <;> simp_all

theorem den_zero (next : Program G A B Aux Data w) : den E F gate UA Ub select next 0 = 0 := by
  have h := Repetition.executeDensity_smul (next.lower E F gate) UA Ub select (0 : ℂ) (0 : Fin w → ℂ)
  simpa using h

theorem den_failure (accepted : Aux → Bool) (out : Fin d) (v : Fin w → ℂ) :
    den E F gate UA Ub select (failure F accepted out) v =
      (Repetition.failureOutput (A:=A) (B:=B) out w).executeDensity UA Ub select v := by
  rw [failure,den_measureAll]
  simp_rw [masked_full,den_reset_basis,den_discard_basis]
  simp only [Sum.elim_inr,Equiv.apply_symm_apply]
  rw [Repetition.failureOutput_executeDensity]
  by_cases hs : select false
  · simp only [hs,ite_true,Repetition.pureDensity_complex_smul,←Finset.sum_smul]
    congr 1
    simpa only [bornMass] using E.sum_comp (fun j=>Complex.normSq (v j))
  · simp [hs]

/-- This is the exact coarse-graining identity of the actual auxiliary-then-data
measurement tree. Only rejection measures data. -/
theorem den_attempt (accepted : Aux → Bool) (zero : State Aux Data)
    (next : Program G A B Aux Data w) (v : Fin w → ℂ) :
    den E F gate UA Ub select (attempt accepted zero next) v =
      (if select true then pureDensity
        (Repetition.acceptMatrix (Repetition.reindexEmbedding E F (auxEmbedding accepted)) *ᵥ v) else 0) +
      ∑ j : Fin w, den E F gate UA Ub select next
        (Repetition.resetMatrix (Repetition.reindexEmbedding E F (auxEmbedding accepted)) (E zero) j *ᵥ v) := by
  let S := if select true then pureDensity
    (Repetition.acceptMatrix (Repetition.reindexEmbedding E F (auxEmbedding accepted)) *ᵥ v) else 0
  let D := fun (a : Aux → Bool) (b : Data → Bool)=>
    den E F gate UA Ub select next (v (E (Sum.elim a b)) • Repetition.basis (E zero))
  have hs : den E F gate UA Ub select (.discard true) (masked E Sum.inl accepted v)=S := by
    rw [den_discard_masked]
    dsimp [S]
    rw [Repetition.acceptMatrix_mulVec]
    rfl
  have hd (a : Aux → Bool) : den E F gate UA Ub select
      (Program.measureAll Sum.inr (fun b=>Program.reset zero (Sum.elim a b) next))
      (masked E Sum.inl a v)=∑ b : Data → Bool, D a b := by
    rw [den_measureAll]
    simp_rw [masked_split,masked_full,den_reset_basis]
    rfl
  rw [attempt,den_measureAll]
  have hbranch (a : Aux → Bool) :
      den E F gate UA Ub select
        (if a=accepted then .discard true else Program.measureAll Sum.inr
          (fun b=>Program.reset zero (Sum.elim a b) next)) (masked E Sum.inl a v) =
        (if a=accepted then S else 0) + ∑ b : Data → Bool, if a=accepted then 0 else D a b := by
    by_cases ha : a=accepted
    · subst a; simp [hs]
    · simp [ha,hd]
  simp_rw [hbranch]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  change S + _ = S + _
  congr 1
  let e : ((Aux → Bool) × (Data → Bool)) ≃ Fin w :=
    (PhysicalMeasurement.productBits (Equiv.refl _) (Equiv.refl _)).trans E
  have hsum := Fintype.sum_equiv e
    (fun p : (Aux → Bool) × (Data → Bool)=>if p.1=accepted then 0 else D p.1 p.2)
    (fun j=>den E F gate UA Ub select next
      (Repetition.resetMatrix (Repetition.reindexEmbedding E F (auxEmbedding accepted)) (E zero) j *ᵥ v))
    (by
      intro p
      rcases p with ⟨a,b⟩
      change (if a=accepted then 0 else D a b) =
        den E F gate UA Ub select next
          (Repetition.resetMatrix (Repetition.reindexEmbedding E F (auxEmbedding accepted))
            (E zero) (E (Sum.elim a b)) *ᵥ v)
      rw [Repetition.resetMatrix_mulVec]
      have he : (∃ i, Repetition.reindexEmbedding E F (auxEmbedding accepted) i=E (Sum.elim a b)) ↔ a=accepted := by
        rw [reindexed_aux_range]
        simp only [Sum.elim_inl,← funext_iff]
      simp only [Repetition.rejectAmplitude,he]
      by_cases ha : a=accepted
      · simp [ha,den_zero]
      · simp [ha,D])
  rw [Fintype.sum_prod_type] at hsum
  exact hsum

/-- All vectors, all oracle unitaries, all flags, and every retry count. The
costed tree's lowering refines the same repeatProgram used for correctness. -/
theorem repeated_refines (c : NamedCircuit G A B (Fin w)) (accepted : Aux → Bool)
    (zero : State Aux Data) (out : Fin d) (R : ℕ) (v : Fin w → ℂ) :
    den E F gate UA Ub select (repeated F c accepted zero out R) v =
      (Repetition.repeatProgram (c.toQuery gate)
        (Repetition.reindexEmbedding E F (auxEmbedding accepted)) (E zero) out R).executeDensity UA Ub select v := by
  induction R generalizing v with
  | zero => exact den_failure E F gate UA Ub select accepted out v
  | succ R ih =>
    simp only [repeated,den,Program.lower_prepend,Repetition.prepend_executeDensity]
    rw [← den,den_attempt]
    simp_rw [ih]
    rw [Repetition.repeatProgram,Repetition.prepend_executeDensity]
    simp only [FiniteOracleProgram.executeDensity,Fin.sum_univ_succ]
    rfl

end OptimalQLS.Refinement.CostedExecution
