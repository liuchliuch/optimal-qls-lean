import OptimalQLS.Refinement.CostedExecution.Syntax

/-! The actual repeated physical program, including terminal failure cleanup. -/
noncomputable section
open scoped Classical
namespace OptimalQLS.Refinement.CostedExecution
open Matrix PolynomialTransform Repetition.Physical
set_option maxHeartbeats 500000
variable {G A B Aux Data : Type*} [Fintype Aux] [DecidableEq Aux]
  [Fintype Data] [DecidableEq Data] {d w : ℕ}

/-- Final failure is physically measured/reset on every existing bit; its
auxiliaries are discarded only after the known failure basis word is prepared. -/
def failure (F : (Data → Bool) ≃ Fin d) (accepted : Aux → Bool) (out : Fin d) :
    Program G A B Aux Data w :=
  Program.measureAll id (fun observed=>Program.reset (Sum.elim accepted (F.symm out)) observed
    (.discard false))

/-- The post-unitary physical acceptance/retry tree. -/
def attempt (accepted : Aux → Bool) (zero : State Aux Data)
    (next : Program G A B Aux Data w) : Program G A B Aux Data w :=
  Program.measureAll Sum.inl (fun a=>
    if a=accepted then .discard true else
      Program.measureAll Sum.inr (fun b=>Program.reset zero (Sum.elim a b) next))

/-- On acceptance, no data bit is measured. On rejection, exactly the remaining
data bits are measured, then conditional X gates reset the entire same register. -/
def repeated (F : (Data → Bool) ≃ Fin d) (c : NamedCircuit G A B (Fin w))
    (accepted : Aux → Bool) (zero : State Aux Data) (out : Fin d) : ℕ → Program G A B Aux Data w
  | 0 => failure F accepted out
  | R+1 => Program.prepend c (attempt accepted zero (repeated F c accepted zero out R))

theorem failure_cost (F : (Data → Bool) ≃ Fin d) (accepted : Aux → Bool) (out : Fin d) :
    (failure (G:=G) (A:=A) (B:=B) (w:=w) F accepted out).cost ≤ 2*Fintype.card (Wire Aux Data) := by
  unfold failure
  have h := Program.cost_measureAll (G:=G) (A:=A) (B:=B) (w:=w) id
    (fun observed=>Program.reset (Sum.elim accepted (F.symm out)) observed (.discard false))
    (Fintype.card (Wire Aux Data)) (fun observed=>by simpa [Program.cost] using
      (Program.cost_reset (Sum.elim accepted (F.symm out)) observed
        (Program.discard (G:=G) (A:=A) (B:=B) (w:=w) false)))
  omega

/-- The worst path cost is extracted from the emitted primitive tree itself. -/
theorem repeat_cost (F : (Data → Bool) ≃ Fin d) (c : NamedCircuit G A B (Fin w))
    (accepted : Aux → Bool) (zero : State Aux Data) (out : Fin d) (R : ℕ) :
    (repeated F c accepted zero out R).cost ≤
      R*(c.workGates+Fintype.card Aux+2*Fintype.card (Wire Aux Data))+
        2*Fintype.card (Wire Aux Data) := by
  induction R with
  | zero => simpa [repeated] using failure_cost (G:=G) (A:=A) (B:=B) (w:=w) F accepted out
  | succ R ih =>
    rw [repeated,Program.cost_prepend,attempt]
    have hh := Program.cost_measureAll Sum.inl
      (fun a=>if a=accepted then Program.discard (G:=G) (A:=A) (B:=B) (w:=w) true else
        Program.measureAll Sum.inr (fun b=>Program.reset zero (Sum.elim a b)
          (repeated F c accepted zero out R)))
      (Fintype.card Data+Fintype.card (Wire Aux Data)+(repeated F c accepted zero out R).cost)
      (by
        intro a
        dsimp only
        split_ifs
        · exact Nat.zero_le _
        · have hd := Program.cost_measureAll Sum.inr
            (fun b=>Program.reset zero (Sum.elim a b) (repeated F c accepted zero out R))
            (Fintype.card (Wire Aux Data)+(repeated F c accepted zero out R).cost)
            (fun b=>Program.cost_reset zero (Sum.elim a b) (repeated F c accepted zero out R))
          simpa [Nat.add_assoc] using hd)
    have hc : Fintype.card Data≤Fintype.card (Wire Aux Data) := by
      simp [Wire,Fintype.card_sum]
    simp only [Nat.add_mul,Nat.one_mul]
    omega

end OptimalQLS.Refinement.CostedExecution
