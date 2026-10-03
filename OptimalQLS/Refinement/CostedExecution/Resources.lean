import OptimalQLS.Refinement.CostedExecution.Repeated
import OptimalQLS.Refinement.CostedExecution.Paths

/-! Oracle depths and live-register bounds of the same primitive tree. -/
noncomputable section
open scoped Classical
namespace OptimalQLS.Refinement.CostedExecution
open Matrix LowerBounds PolynomialTransform
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
variable {G A B Aux Data : Type*} [Fintype Aux] [DecidableEq Aux]
  [Fintype Data] [DecidableEq Data] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  {d w : ℕ}

private theorem sup_two (f : Fin 2 → ℕ) : Finset.univ.sup f=max (f 0) (f 1) := by
  apply le_antisymm
  · apply Finset.sup_le
    intro i _
    fin_cases i
    · exact Nat.le_max_left _ _
    · exact Nat.le_max_right _ _
  · exact max_le (Finset.le_sup (f:=f) (Finset.mem_univ 0))
      (Finset.le_sup (f:=f) (Finset.mem_univ 1))

namespace Program

theorem lower_matrixCalls (E : State Aux Data ≃ Fin w) (F : (Data → Bool) ≃ Fin d)
    (gate : G → Matrix.unitaryGroup (Fin w) ℂ) (p : Program G A B Aux Data w) :
    Repetition.matrixDepth (p.lower E F gate)=p.matrixCalls := by
  induction p with
  | named g next ih => simpa [lower,Repetition.matrixDepth,matrixCalls] using ih
  | matrixCall p b next ih => simp [lower,Repetition.matrixDepth,matrixCalls,ih]
  | vectorCall p b next ih => exact ih
  | measure i next ih => simp only [lower,Repetition.matrixDepth,ih,sup_two,matrixCalls]; rfl
  | bitX i next ih => simpa [lower,Repetition.matrixDepth,matrixCalls] using ih
  | discard flag => simp [lower,Repetition.matrixDepth,matrixCalls]

theorem lower_vectorCalls (E : State Aux Data ≃ Fin w) (F : (Data → Bool) ≃ Fin d)
    (gate : G → Matrix.unitaryGroup (Fin w) ℂ) (p : Program G A B Aux Data w) :
    (p.lower E F gate).vectorDepth=p.vectorCalls := by
  induction p with
  | named g next ih => simpa [lower,FiniteOracleProgram.vectorDepth,vectorCalls] using ih
  | matrixCall p b next ih => exact ih
  | vectorCall p b next ih => simp [lower,FiniteOracleProgram.vectorDepth,vectorCalls,ih]
  | measure i next ih => simp only [lower,FiniteOracleProgram.vectorDepth,ih,sup_two,vectorCalls]; rfl
  | bitX i next ih => simpa [lower,FiniteOracleProgram.vectorDepth,vectorCalls] using ih
  | discard flag => simp [lower,FiniteOracleProgram.vectorDepth,vectorCalls]

/-- Lowering preserves each charged primitive node exactly. The one additional
instrument is the terminal partial trace, which is not charged as a gate. -/
theorem lower_instrumentDepth (E : State Aux Data ≃ Fin w) (F : (Data → Bool) ≃ Fin d)
    (gate : G → Matrix.unitaryGroup (Fin w) ℂ) (p : Program G A B Aux Data w) :
    Repetition.instrumentDepth (p.lower E F gate)=p.cost+1 := by
  induction p with
  | named g next ih => simp [lower,Repetition.instrumentDepth,cost,ih]
  | matrixCall p b next ih => exact ih
  | vectorCall p b next ih => exact ih
  | measure i next ih =>
    simp only [lower,Repetition.instrumentDepth,ih,sup_two,cost]
    simp [outcome,max_add_add_right]
  | bitX i next ih => simp [lower,Repetition.instrumentDepth,cost,ih]
  | discard flag => simp [lower,Repetition.instrumentDepth,cost]

/-- Neither measurement nor reset allocates a quantum-history register. -/
theorem lower_registerBound (E : State Aux Data ≃ Fin w) (F : (Data → Bool) ≃ Fin d)
    (gate : G → Matrix.unitaryGroup (Fin w) ℂ) (p : Program G A B Aux Data w) :
    Repetition.RegisterBound w (p.lower E F gate) := by
  have hd : d≤w := by
    let embed : Fin d ↪ Fin w := Repetition.reindexEmbedding E F
      (Repetition.Physical.auxEmbedding (fun _=>false))
    simpa using Fintype.card_le_of_injective embed embed.injective
  induction p with
  | named g next ih => exact ⟨le_rfl,fun _=>ih⟩
  | matrixCall p b next ih => exact ⟨le_rfl,ih⟩
  | vectorCall p b next ih => exact ⟨le_rfl,ih⟩
  | measure i next ih => exact ⟨le_rfl,fun b=>ih (outcome b)⟩
  | bitX i next ih => exact ⟨le_rfl,fun _=>ih⟩
  | discard flag => exact ⟨le_rfl,fun _=>hd⟩

theorem matrixCalls_prepend (c : NamedCircuit G A B (Fin w))
    (gate : G → Matrix.unitaryGroup (Fin w) ℂ) (next : Program G A B Aux Data w) :
    (prepend c next).matrixCalls=(c.toQuery gate).matrixQueries+next.matrixCalls := by
  induction c with
  | nil => simp [prepend,NamedCircuit.toQuery,QueryCircuit.matrixQueries]
  | cons g c ih => cases g <;> simp [prepend,matrixCalls,NamedCircuit.toQuery,
      NamedInstruction.toQuery,QueryCircuit.matrixQueries] at ih ⊢ <;> omega

theorem vectorCalls_prepend (c : NamedCircuit G A B (Fin w))
    (gate : G → Matrix.unitaryGroup (Fin w) ℂ) (next : Program G A B Aux Data w) :
    (prepend c next).vectorCalls=(c.toQuery gate).vectorQueries+next.vectorCalls := by
  induction c with
  | nil => simp [prepend,NamedCircuit.toQuery,QueryCircuit.vectorQueries]
  | cons g c ih => cases g <;> simp [prepend,vectorCalls,NamedCircuit.toQuery,
      NamedInstruction.toQuery,QueryCircuit.vectorQueries] at ih ⊢ <;> omega

theorem measureFin_matrixCalls_le (k : ℕ) (wire : Fin k → Wire Aux Data)
    (next : (Fin k → Bool) → Program G A B Aux Data w) (N : ℕ)
    (hn : ∀ bs, (next bs).matrixCalls≤N) : (measureFin k wire next).matrixCalls≤N := by
  induction k with
  | zero => exact hn _
  | succ k ih =>
    simp only [measureFin,matrixCalls]
    exact max_le (ih _ _ (fun bs=>hn _)) (ih _ _ (fun bs=>hn _))

theorem measureFin_vectorCalls_le (k : ℕ) (wire : Fin k → Wire Aux Data)
    (next : (Fin k → Bool) → Program G A B Aux Data w) (N : ℕ)
    (hn : ∀ bs, (next bs).vectorCalls≤N) : (measureFin k wire next).vectorCalls≤N := by
  induction k with
  | zero => exact hn _
  | succ k ih =>
    simp only [measureFin,vectorCalls]
    exact max_le (ih _ _ (fun bs=>hn _)) (ih _ _ (fun bs=>hn _))

theorem measureAll_matrixCalls_le {I : Type*} [Fintype I] (wire : I → Wire Aux Data)
    (next : (I → Bool) → Program G A B Aux Data w) (N : ℕ)
    (hn : ∀ bs, (next bs).matrixCalls≤N) : (measureAll wire next).matrixCalls≤N :=
  measureFin_matrixCalls_le _ _ _ _ (fun _=>hn _)

theorem measureAll_vectorCalls_le {I : Type*} [Fintype I] (wire : I → Wire Aux Data)
    (next : (I → Bool) → Program G A B Aux Data w) (N : ℕ)
    (hn : ∀ bs, (next bs).vectorCalls≤N) : (measureAll wire next).vectorCalls≤N :=
  measureFin_vectorCalls_le _ _ _ _ (fun _=>hn _)

theorem feedback_matrixCalls (target observed : State Aux Data) (wires : List (Wire Aux Data))
    (next : Program G A B Aux Data w) : (feedback target observed wires next).matrixCalls=next.matrixCalls := by
  induction wires generalizing next with
  | nil => rfl
  | cons i wires ih => rw [feedback,ih]; split_ifs <;> rfl

theorem feedback_vectorCalls (target observed : State Aux Data) (wires : List (Wire Aux Data))
    (next : Program G A B Aux Data w) : (feedback target observed wires next).vectorCalls=next.vectorCalls := by
  induction wires generalizing next with
  | nil => rfl
  | cons i wires ih => rw [feedback,ih]; split_ifs <;> rfl

theorem measureFin_matrixCalls_ge (k : ℕ) (wire : Fin k → Wire Aux Data)
    (next : (Fin k → Bool) → Program G A B Aux Data w) (bs : Fin k → Bool) :
    (next bs).matrixCalls≤(measureFin k wire next).matrixCalls := by
  induction k with
  | zero => have he : bs=Fin.elim0 := Subsingleton.elim _ _; subst bs; exact le_rfl
  | succ k ih =>
    have he : Fin.cons (bs 0) (fun i=>bs i.succ)=bs := by ext i; refine Fin.cases ?_ (fun j=>?_) i <;> rfl
    have hh := ih (fun i=>wire i.succ) (fun tail=>next (Fin.cons (bs 0) tail)) (fun i=>bs i.succ)
    rw [he] at hh
    simp only [measureFin,matrixCalls]
    cases hb : bs 0
    · rw [hb] at hh; exact hh.trans (Nat.le_max_left _ _)
    · rw [hb] at hh; exact hh.trans (Nat.le_max_right _ _)

theorem measureFin_vectorCalls_ge (k : ℕ) (wire : Fin k → Wire Aux Data)
    (next : (Fin k → Bool) → Program G A B Aux Data w) (bs : Fin k → Bool) :
    (next bs).vectorCalls≤(measureFin k wire next).vectorCalls := by
  induction k with
  | zero => have he : bs=Fin.elim0 := Subsingleton.elim _ _; subst bs; exact le_rfl
  | succ k ih =>
    have he : Fin.cons (bs 0) (fun i=>bs i.succ)=bs := by ext i; refine Fin.cases ?_ (fun j=>?_) i <;> rfl
    have hh := ih (fun i=>wire i.succ) (fun tail=>next (Fin.cons (bs 0) tail)) (fun i=>bs i.succ)
    rw [he] at hh
    simp only [measureFin,vectorCalls]
    cases hb : bs 0
    · rw [hb] at hh; exact hh.trans (Nat.le_max_left _ _)
    · rw [hb] at hh; exact hh.trans (Nat.le_max_right _ _)

theorem measureAll_matrixCalls_ge {I : Type*} [Fintype I] (wire : I → Wire Aux Data)
    (next : (I → Bool) → Program G A B Aux Data w) (bs : I → Bool) :
    (next bs).matrixCalls≤(measureAll wire next).matrixCalls := by
  have hh := measureFin_matrixCalls_ge (Fintype.card I)
    (fun i=>wire ((Fintype.equivFin I).symm i))
    (fun b=>next (b ∘ Fintype.equivFin I)) (bs ∘ (Fintype.equivFin I).symm)
  simpa only [Function.comp_assoc,Equiv.symm_comp_self,Function.comp_id] using hh

theorem measureAll_vectorCalls_ge {I : Type*} [Fintype I] (wire : I → Wire Aux Data)
    (next : (I → Bool) → Program G A B Aux Data w) (bs : I → Bool) :
    (next bs).vectorCalls≤(measureAll wire next).vectorCalls := by
  have hh := measureFin_vectorCalls_ge (Fintype.card I)
    (fun i=>wire ((Fintype.equivFin I).symm i))
    (fun b=>next (b ∘ Fintype.equivFin I)) (bs ∘ (Fintype.equivFin I).symm)
  simpa only [Function.comp_assoc,Equiv.symm_comp_self,Function.comp_id] using hh
end Program

theorem failure_calls (F : (Data → Bool) ≃ Fin d) (accepted : Aux → Bool) (out : Fin d) :
    (failure (G:=G) (A:=A) (B:=B) (w:=w) F accepted out).matrixCalls=0 ∧
    (failure (G:=G) (A:=A) (B:=B) (w:=w) F accepted out).vectorCalls=0 := by
  constructor
  · apply Nat.eq_zero_of_le_zero
    apply Program.measureAll_matrixCalls_le
    intro observed
    simp [Program.reset,Program.feedback_matrixCalls,Program.matrixCalls]
  · apply Nat.eq_zero_of_le_zero
    apply Program.measureAll_vectorCalls_le
    intro observed
    simp [Program.reset,Program.feedback_vectorCalls,Program.vectorCalls]

theorem attempt_calls_le (accepted : Aux → Bool) (zero : State Aux Data)
    (next : Program G A B Aux Data w) :
    (attempt accepted zero next).matrixCalls≤next.matrixCalls ∧
    (attempt accepted zero next).vectorCalls≤next.vectorCalls := by
  constructor
  · apply Program.measureAll_matrixCalls_le
    intro a
    dsimp only
    split_ifs
    · exact Nat.zero_le _
    · apply Program.measureAll_matrixCalls_le
      intro b
      simp [Program.reset,Program.feedback_matrixCalls]
  · apply Program.measureAll_vectorCalls_le
    intro a
    dsimp only
    split_ifs
    · exact Nat.zero_le _
    · apply Program.measureAll_vectorCalls_le
      intro b
      simp [Program.reset,Program.feedback_vectorCalls]

theorem attempt_calls [Nonempty Aux] (accepted : Aux → Bool) (zero : State Aux Data)
    (next : Program G A B Aux Data w) :
    (attempt accepted zero next).matrixCalls=next.matrixCalls ∧
    (attempt accepted zero next).vectorCalls=next.vectorCalls := by
  let a : Aux → Bool := fun i=> !(accepted i)
  have ha : a≠accepted := by
    intro h
    have hh := congrFun h (Classical.choice (inferInstance : Nonempty Aux))
    dsimp [a] at hh
    cases accepted (Classical.choice (inferInstance : Nonempty Aux)) <;> simp at hh
  constructor
  · apply le_antisymm (attempt_calls_le accepted zero next).1
    have hh := Program.measureAll_matrixCalls_ge Sum.inl
      (fun a=>if a=accepted then Program.discard true else Program.measureAll Sum.inr
        (fun b=>Program.reset zero (Sum.elim a b) next)) a
    simp only [if_neg ha] at hh
    have hd := Program.measureAll_matrixCalls_ge Sum.inr
      (fun b=>Program.reset zero (Sum.elim a b) next) (fun _=>false)
    rw [Program.reset,Program.feedback_matrixCalls] at hd
    exact hd.trans hh
  · apply le_antisymm (attempt_calls_le accepted zero next).2
    have hh := Program.measureAll_vectorCalls_ge Sum.inl
      (fun a=>if a=accepted then Program.discard true else Program.measureAll Sum.inr
        (fun b=>Program.reset zero (Sum.elim a b) next)) a
    simp only [if_neg ha] at hh
    have hd := Program.measureAll_vectorCalls_ge Sum.inr
      (fun b=>Program.reset zero (Sum.elim a b) next) (fun _=>false)
    rw [Program.reset,Program.feedback_vectorCalls] at hd
    exact hd.trans hh

/-- Exact worst-case query counts, not merely asymptotic bounds. The full tree
contains a rejection branch even when its actual amplitude happens to vanish. -/
theorem repeated_calls [Nonempty Aux] (F : (Data → Bool) ≃ Fin d)
    (c : NamedCircuit G A B (Fin w)) (gate : G → Matrix.unitaryGroup (Fin w) ℂ)
    (accepted : Aux → Bool) (zero : State Aux Data) (out : Fin d) (R : ℕ) :
    (repeated F c accepted zero out R).matrixCalls=R*(c.toQuery gate).matrixQueries ∧
    (repeated F c accepted zero out R).vectorCalls=R*(c.toQuery gate).vectorQueries := by
  induction R with
  | zero => simpa [repeated] using failure_calls (G:=G) (A:=A) (B:=B) (w:=w) F accepted out
  | succ R ih =>
    simp only [repeated,Program.matrixCalls_prepend c gate,Program.vectorCalls_prepend c gate,
      (attempt_calls _ _ _).1,(attempt_calls _ _ _).2,ih.1,ih.2,Nat.add_mul,Nat.one_mul]
    omega

end OptimalQLS.Refinement.CostedExecution
