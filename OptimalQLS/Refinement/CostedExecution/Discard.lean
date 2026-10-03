import OptimalQLS.Refinement.CostedExecution.Semantics

/-! Exact behavior of discarding measured, hence known, auxiliaries. -/
noncomputable section
open scoped BigOperators Classical
namespace OptimalQLS.Refinement.CostedExecution
open Matrix LowerBounds Repetition.Physical
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
variable {G A B Aux Data : Type*} [Fintype Aux] [DecidableEq Aux]
  [Fintype Data] [DecidableEq Data] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  {d w : ℕ}
variable (E : State Aux Data ≃ Fin w) (F : (Data → Bool) ≃ Fin d)
  (gate : G → Matrix.unitaryGroup (Fin w) ℂ)
  (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (select : Bool → Bool)

theorem den_discard (flag : Bool) (v : Fin w → ℂ) :
    den E F gate UA Ub select (.discard flag) v =
      ∑ a : Aux → Bool, if select flag then pureDensity (discardKraus E F a *ᵥ v) else 0 := by
  simp only [den,Program.lower,FiniteOracleProgram.executeDensity]
  exact (Fintype.equivFin (Aux → Bool)).symm.sum_comp
    (fun a=>if select flag then pureDensity (discardKraus E F a *ᵥ v) else 0)

theorem discardKraus_masked (a b : Aux → Bool) (v : Fin w → ℂ) :
    discardKraus E F b *ᵥ masked E Sum.inl a v =
      if b=a then (fun i=>v ((split E F).symm (a,i))) else 0 := by
  rw [discardKraus_mulVec]
  have he : (∀ i, b i=a i) ↔ b=a := funext_iff.symm
  funext i
  have hx : E.symm ((split E F).symm (b,i))=Sum.elim b (F.symm i) := E.symm_apply_apply _
  simp only [masked,hx,Sum.elim_inl,he]
  split_ifs with h
  · subst b; rfl
  · rfl

theorem den_discard_masked (flag : Bool) (a : Aux → Bool) (v : Fin w → ℂ) :
    den E F gate UA Ub select (.discard flag) (masked E Sum.inl a v) =
      if select flag then pureDensity (fun i=>v ((split E F).symm (a,i))) else 0 := by
  rw [den_discard]
  simp_rw [discardKraus_masked]
  by_cases hs : select flag
  · simp only [hs,ite_true]
    have hz : pureDensity (0 : Fin d → ℂ)=0 := by ext i j; simp [pureDensity,ketBra,Matrix.vecMulVec]
    try simp only [smul_ite,smul_zero]
    simp_rw [apply_ite pureDensity, hz]
    simp
  · simp [hs]

theorem discardKraus_basis (a : Aux → Bool) (s : State Aux Data) :
    discardKraus E F a *ᵥ Repetition.basis (E s) =
      if a=(fun i=>s (.inl i)) then Repetition.basis (F (fun i=>s (.inr i))) else 0 := by
  rw [discardKraus_mulVec]
  funext i
  have he : (split E F).symm (a,i)=E s ↔ a=(fun i=>s (.inl i)) ∧ i=F (fun i=>s (.inr i)) := by
    rw [(split E F).symm_apply_eq]
    simp [split,Prod.ext_iff]
  simp only [Repetition.basis,he]
  split_ifs <;> simp_all [Repetition.basis]

theorem den_discard_basis (flag : Bool) (s : State Aux Data) (z : ℂ) :
    den E F gate UA Ub select (.discard flag) (z • Repetition.basis (E s)) =
      if select flag then pureDensity (z • Repetition.basis (F (fun i=>s (.inr i)))) else 0 := by
  rw [den_discard]
  simp_rw [Matrix.mulVec_smul,discardKraus_basis]
  by_cases hs : select flag
  · simp only [hs,ite_true]
    have hz : pureDensity (0 : Fin d → ℂ)=0 := by ext i j; simp [pureDensity,ketBra,Matrix.vecMulVec]
    try simp only [smul_ite,smul_zero]
    simp_rw [apply_ite pureDensity, hz]
    simp
  · simp [hs]

end OptimalQLS.Refinement.CostedExecution
