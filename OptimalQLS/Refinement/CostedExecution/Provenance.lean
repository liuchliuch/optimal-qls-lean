import OptimalQLS.Refinement.CostedExecution.Repeated

/-! The primitive tree contains only the named gates and query ports supplied
by its literal run list. Measurement and feedback add no oracle calls. -/
noncomputable section
open scoped Classical
namespace OptimalQLS.Refinement.CostedExecution
open Matrix PolynomialTransform
variable {G A B Aux Data : Type*} [Fintype Aux] [DecidableEq Aux]
  [Fintype Data] [DecidableEq Data] {d w : ℕ}

namespace Program

def Allowed (gok : G → Prop) (mok : QueryPort A (Fin w) → Bool → Prop)
    (vok : QueryPort B (Fin w) → Bool → Prop) : Program G A B Aux Data w → Prop
  | .named g next => gok g ∧ next.Allowed gok mok vok
  | .matrixCall p b next => mok p b ∧ next.Allowed gok mok vok
  | .vectorCall p b next => vok p b ∧ next.Allowed gok mok vok
  | .measure _ next => ∀ b,(next b).Allowed gok mok vok
  | .bitX _ next => next.Allowed gok mok vok
  | .discard _ => True

def allowedInstruction (gok : G → Prop) (mok : QueryPort A (Fin w) → Bool → Prop)
    (vok : QueryPort B (Fin w) → Bool → Prop) : NamedInstruction G A B (Fin w) → Prop
  | .gate g => gok g
  | .matrixCall p b => mok p b
  | .vectorCall p b => vok p b

variable (gok : G → Prop) (mok : QueryPort A (Fin w) → Bool → Prop)
  (vok : QueryPort B (Fin w) → Bool → Prop)

theorem allowed_prepend (c : NamedCircuit G A B (Fin w)) (next : Program G A B Aux Data w)
    (hc : ∀ i∈c,allowedInstruction gok mok vok i) (hn : next.Allowed gok mok vok) :
    (prepend c next).Allowed gok mok vok := by
  induction c with
  | nil => exact hn
  | cons g c ih =>
    have ht := ih (fun i hi=>hc i (List.mem_cons_of_mem _ hi))
    have hg := hc g (by simp)
    cases g <;> exact ⟨hg,ht⟩

theorem allowed_measureFin (k : ℕ) (wire : Fin k → Wire Aux Data)
    (next : (Fin k → Bool) → Program G A B Aux Data w)
    (hn : ∀ bs,(next bs).Allowed gok mok vok) :
    (measureFin k wire next).Allowed gok mok vok := by
  induction k with
  | zero => exact hn _
  | succ k ih => exact fun b=>ih _ _ (fun bs=>hn _)

theorem allowed_measureAll {I : Type*} [Fintype I] (wire : I → Wire Aux Data)
    (next : (I → Bool) → Program G A B Aux Data w)
    (hn : ∀ bs,(next bs).Allowed gok mok vok) :
    (measureAll wire next).Allowed gok mok vok :=
  allowed_measureFin gok mok vok _ _ _ (fun bs=>hn _)

theorem allowed_feedback (target observed : State Aux Data) (wires : List (Wire Aux Data))
    (next : Program G A B Aux Data w) (hn : next.Allowed gok mok vok) :
    (feedback target observed wires next).Allowed gok mok vok := by
  induction wires generalizing next with
  | nil => exact hn
  | cons i wires ih =>
    apply ih
    split_ifs <;> exact hn

theorem allowed_reset (target observed : State Aux Data)
    (next : Program G A B Aux Data w) (hn : next.Allowed gok mok vok) :
    (reset target observed next).Allowed gok mok vok :=
  allowed_feedback gok mok vok _ _ _ _ hn
end Program

variable (gok : G → Prop) (mok : QueryPort A (Fin w) → Bool → Prop)
  (vok : QueryPort B (Fin w) → Bool → Prop)

theorem allowed_failure (F : (Data → Bool) ≃ Fin d) (accepted : Aux → Bool) (out : Fin d) :
    (failure (G:=G) (A:=A) (B:=B) (w:=w) F accepted out).Allowed gok mok vok := by
  apply Program.allowed_measureAll
  intro observed
  apply Program.allowed_reset
  trivial

theorem allowed_attempt (accepted : Aux → Bool) (zero : State Aux Data)
    (next : Program G A B Aux Data w) (hn : next.Allowed gok mok vok) :
    (attempt accepted zero next).Allowed gok mok vok := by
  apply Program.allowed_measureAll
  intro a
  dsimp only
  split_ifs
  · trivial
  · apply Program.allowed_measureAll
    intro b
    exact Program.allowed_reset _ _ _ _ _ _ hn

theorem allowed_repeated (F : (Data → Bool) ≃ Fin d) (c : NamedCircuit G A B (Fin w))
    (accepted : Aux → Bool) (zero : State Aux Data) (out : Fin d) (R : ℕ)
    (hc : ∀ i∈c,Program.allowedInstruction gok mok vok i) :
    (repeated F c accepted zero out R).Allowed gok mok vok := by
  induction R with
  | zero => exact allowed_failure _ _ _ _ _ _
  | succ R ih =>
    apply Program.allowed_prepend _ _ _ _ _ hc
    exact allowed_attempt _ _ _ _ _ _ ih

end OptimalQLS.Refinement.CostedExecution
