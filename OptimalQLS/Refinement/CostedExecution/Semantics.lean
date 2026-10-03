import OptimalQLS.Refinement.CostedExecution.Syntax

/-! Exact branch expansion of the primitive measurement/reset syntax. -/
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

abbrev den (p : Program G A B Aux Data w) (v : Fin w → ℂ) :=
  (p.lower E F gate).executeDensity UA Ub select v

theorem bitKraus_diagonal (i : Wire Aux Data) (b : Bool) :
    bitKraus E i b = diagonal (fun j=>if E.symm j i=b then 1 else 0) := by
  ext j k
  simp [bitKraus,bitProjector,Matrix.diagonal,Matrix.submatrix,E.symm.injective.eq_iff]

theorem bitKraus_mulVec (i : Wire Aux Data) (b : Bool) (v : Fin w → ℂ) :
    bitKraus E i b *ᵥ v = fun j=>if E.symm j i=b then v j else 0 := by
  rw [bitKraus_diagonal]
  ext j
  simp [Matrix.mulVec_diagonal]

/-- Branch state after a finite list of individually observed bits. -/
def masked {I : Type*} (wire : I → Wire Aux Data) (bs : I → Bool) (v : Fin w → ℂ) : Fin w → ℂ :=
  fun j=>if ∀ i, E.symm j (wire i)=bs i then v j else 0

theorem masked_cons (k : ℕ) (wire : Fin (k+1) → Wire Aux Data) (b : Bool)
    (bs : Fin k → Bool) (v : Fin w → ℂ) :
    masked E (fun i=>wire i.succ) bs (bitKraus E (wire 0) b *ᵥ v) =
      masked E wire (Fin.cons b bs) v := by
  rw [bitKraus_mulVec]
  funext j
  simp only [masked,Fin.forall_fin_succ,Fin.cons_zero,Fin.cons_succ]
  split_ifs <;> simp_all

theorem den_measure (i : Wire Aux Data) (next : Bool → Program G A B Aux Data w)
    (v : Fin w → ℂ) :
    den E F gate UA Ub select (.measure i next) v =
      ∑ b : Bool, den E F gate UA Ub select (next b) (bitKraus E i b *ᵥ v) := by
  simp only [den,Program.lower,FiniteOracleProgram.executeDensity]
  exact outcome.sum_comp (fun b=>den E F gate UA Ub select (next b) (bitKraus E i b *ᵥ v))

theorem den_measureFin (k : ℕ) (wire : Fin k → Wire Aux Data)
    (next : (Fin k → Bool) → Program G A B Aux Data w) (v : Fin w → ℂ) :
    den E F gate UA Ub select (Program.measureFin k wire next) v =
      ∑ bs : Fin k → Bool, den E F gate UA Ub select (next bs) (masked E wire bs v) := by
  induction k generalizing v with
  | zero =>
    have hm : masked E wire Fin.elim0 v=v := by ext j; simp [masked]
    simp only [Program.measureFin]
    rw [Fintype.sum_unique]
    congr 1
    ext j; simp [masked]
  | succ k ih =>
    rw [Program.measureFin,den_measure]
    simp_rw [ih,masked_cons]
    have h := (Fin.consEquiv (fun _ : Fin (k+1)=>Bool)).sum_comp
      (fun bs=>den E F gate UA Ub select (next bs) (masked E wire bs v))
    rw [Fintype.sum_prod_type] at h
    exact h

/-- Each possible classical bit word occurs exactly once in the expansion. -/
theorem den_measureAll {I : Type*} [Fintype I] [DecidableEq I] (wire : I → Wire Aux Data)
    (next : (I → Bool) → Program G A B Aux Data w) (v : Fin w → ℂ) :
    den E F gate UA Ub select (Program.measureAll wire next) v =
      ∑ bs : I → Bool, den E F gate UA Ub select (next bs) (masked E wire bs v) := by
  rw [Program.measureAll,den_measureFin]
  let e : (Fin (Fintype.card I) → Bool) ≃ (I → Bool) :=
    Equiv.piCongrLeft (fun _ : I=>Bool) (Fintype.equivFin I).symm
  apply Fintype.sum_equiv e
  intro bs
  have hb : e bs=bs ∘ Fintype.equivFin I := by
    funext i
    simp [e,Equiv.piCongrLeft]
  rw [hb]
  congr 1
  ext j
  simp only [masked,Function.comp_apply]
  congr 1
  apply propext
  constructor
  · intro h i; simpa using h (Fintype.equivFin I i)
  · intro h i; simpa using h ((Fintype.equivFin I).symm i)

theorem masked_full (observed : State Aux Data) (v : Fin w → ℂ) :
    masked E id observed v = v (E observed) • Repetition.basis (E observed) := by
  ext j
  have he : (∀ i, E.symm j i=observed i) ↔ j=E observed := by
    rw [← funext_iff,Equiv.symm_apply_eq]
  simp [masked,he,Repetition.basis]
  split_ifs with h <;> simp_all

theorem xGate_basis (i : Wire Aux Data) (s : State Aux Data) :
    (xGate E i).val *ᵥ Repetition.basis (E s) = Repetition.basis (E (bitFlip i s)) := by
  rw [xGate,TransducerCompiler.rewire_apply,TransducerCompiler.permutation_apply]
  ext j
  have he : E (bitFlip i (E.symm j))=E s ↔ j=E (bitFlip i s) := by
    rw [E.injective.eq_iff]
    change bitFlipEquiv i (E.symm j)=s ↔ _
    rw [(bitFlipEquiv i).apply_eq_iff_eq_symm_apply]
    change E.symm j=bitFlip i s ↔ _
    exact E.symm_apply_eq
  simp [Repetition.basis,Function.comp_apply,he,bitFlipEquiv]

theorem den_feedback_basis (target observed : State Aux Data) (wires : List (Wire Aux Data))
    (next : Program G A B Aux Data w) (z : ℂ) :
    den E F gate UA Ub select (Program.feedback target observed wires next)
      (z • Repetition.basis (E observed)) =
    den E F gate UA Ub select next (z • Repetition.basis (E (resetWord target wires observed))) := by
  induction wires generalizing next with
  | nil => rfl
  | cons i wires ih =>
    rw [Program.feedback,ih]
    change den E F gate UA Ub select
      (if resetWord target wires observed i=target i then next else .bitX i next) _ =
      den E F gate UA Ub select next (z • Repetition.basis (E (resetBit target i (resetWord target wires observed))))
    rw [resetBit_is_identity_or_X]
    split_ifs with h
    · rfl
    · simp only [den,Program.lower,FiniteOracleProgram.executeDensity,Fin.sum_univ_one,
        Matrix.mulVec_smul,xGate_basis]

theorem den_reset_basis (target observed : State Aux Data) (next : Program G A B Aux Data w) (z : ℂ) :
    den E F gate UA Ub select (Program.reset target observed next) (z • Repetition.basis (E observed)) =
      den E F gate UA Ub select next (z • Repetition.basis (E target)) := by
  rw [Program.reset,den_feedback_basis,resetWord_full]

end OptimalQLS.Refinement.CostedExecution
