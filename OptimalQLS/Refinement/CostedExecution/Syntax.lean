import OptimalQLS.Refinement.CostedExecution.Primitives
import OptimalQLS.Refinement.Repetition.Resources

/-! A branching physical instruction tree. Every work/measurement/reset operation
is an actual node; cost is extracted recursively from those same nodes. -/
noncomputable section
open scoped BigOperators
namespace OptimalQLS.Refinement.CostedExecution
open Matrix LowerBounds Repetition.Physical PolynomialTransform
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

inductive Program (G A B Aux Data : Type*) (w : ℕ) where
  | named (g : G) (next : Program G A B Aux Data w)
  | matrixCall (p : QueryPort A (Fin w)) (adj : Bool) (next : Program G A B Aux Data w)
  | vectorCall (p : QueryPort B (Fin w)) (adj : Bool) (next : Program G A B Aux Data w)
  | measure (i : Wire Aux Data) (next : Bool → Program G A B Aux Data w)
  | bitX (i : Wire Aux Data) (next : Program G A B Aux Data w)
  | discard (success : Bool)

namespace Program
variable {G A B Aux Data : Type*} {d w : ℕ}

def cost : Program G A B Aux Data w → ℕ
  | .named _ p => p.cost + 1
  | .matrixCall _ _ p => p.cost
  | .vectorCall _ _ p => p.cost
  | .measure _ next => max (next false).cost (next true).cost + 1
  | .bitX _ p => p.cost + 1
  | .discard _ => 0

def matrixCalls : Program G A B Aux Data w → ℕ
  | .named _ p => p.matrixCalls
  | .matrixCall _ _ p => p.matrixCalls + 1
  | .vectorCall _ _ p => p.matrixCalls
  | .measure _ next => max (next false).matrixCalls (next true).matrixCalls
  | .bitX _ p => p.matrixCalls
  | .discard _ => 0

def vectorCalls : Program G A B Aux Data w → ℕ
  | .named _ p => p.vectorCalls
  | .matrixCall _ _ p => p.vectorCalls
  | .vectorCall _ _ p => p.vectorCalls + 1
  | .measure _ next => max (next false).vectorCalls (next true).vectorCalls
  | .bitX _ p => p.vectorCalls
  | .discard _ => 0

variable [Fintype Aux] [DecidableEq Aux] [Fintype Data] [DecidableEq Data]

def lower (E : State Aux Data ≃ Fin w) (F : (Data → Bool) ≃ Fin d)
    (gate : G → Matrix.unitaryGroup (Fin w) ℂ) :
    Program G A B Aux Data w → FiniteOracleProgram A B d w
  | .named g p => .instrument 1 (fun _=>w) (fun _=>(gate g).val)
      (by rw [Fin.sum_univ_one]; exact (gate g).property.1) (fun _=>p.lower E F gate)
  | .matrixCall p adj next => .matrixQuery p adj (next.lower E F gate)
  | .vectorCall p adj next => .vectorQuery p adj (next.lower E F gate)
  | .measure i next => .instrument 2 (fun _=>w) (fun b=>bitKraus E i (outcome b))
      (bitKraus_normalized E i) (fun b=>(next (outcome b)).lower E F gate)
  | .bitX i p => .instrument 1 (fun _=>w) (fun _=>(xGate E i).val)
      (by rw [Fin.sum_univ_one]; exact (xGate E i).property.1) (fun _=>p.lower E F gate)
  | .discard flag => .instrument (Fintype.card (Aux → Bool)) (fun _=>d)
      (fun a=>discardKraus E F ((Fintype.equivFin (Aux → Bool)).symm a))
      (by
        dsimp only
        calc
          _ = ∑ a : Aux → Bool, (discardKraus E F a).conjTranspose * discardKraus E F a :=
            (Fintype.equivFin (Aux → Bool)).symm.sum_comp
              (fun a => (discardKraus E F a).conjTranspose * discardKraus E F a)
          _ = 1 := discardKraus_complete E F)
      (fun _=>.output flag false)

/-- The literal named list is translated one instruction for one node. -/
def prepend (c : NamedCircuit G A B (Fin w)) (next : Program G A B Aux Data w) :
    Program G A B Aux Data w :=
  match c with
  | [] => next
  | .gate g :: c => .named g (prepend c next)
  | .matrixCall p b :: c => .matrixCall p b (prepend c next)
  | .vectorCall p b :: c => .vectorCall p b (prepend c next)

theorem lower_prepend (E : State Aux Data ≃ Fin w) (F : (Data → Bool) ≃ Fin d)
    (gate : G → Matrix.unitaryGroup (Fin w) ℂ) (c : NamedCircuit G A B (Fin w))
    (next : Program G A B Aux Data w) :
    (prepend c next).lower E F gate = Repetition.prepend (c.toQuery gate) (next.lower E F gate) := by
  induction c with
  | nil => rfl
  | cons g c ih => cases g <;> simp [prepend, lower, NamedCircuit.toQuery,
      NamedInstruction.toQuery, Repetition.prepend] at ih ⊢ <;> rw [ih]

theorem cost_prepend (c : NamedCircuit G A B (Fin w)) (next : Program G A B Aux Data w) :
    (prepend c next).cost = c.workGates + next.cost := by
  induction c with
  | nil => simp [prepend,NamedCircuit.workGates]
  | cons g c ih => cases g <;> simp [prepend,cost,NamedCircuit.workGates,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- Sequential one-bit measurements, retaining outcomes only classically. -/
def measureFin : (k : ℕ) → (Fin k → Wire Aux Data) →
    ((Fin k → Bool) → Program G A B Aux Data w) → Program G A B Aux Data w
  | 0, _, next => next Fin.elim0
  | k+1, wires, next => .measure (wires 0)
      (fun b=>measureFin k (fun i=>wires i.succ) (fun bs=>next (Fin.cons b bs)))

def measureAll {I : Type*} [Fintype I] (wire : I → Wire Aux Data)
    (next : (I → Bool) → Program G A B Aux Data w) : Program G A B Aux Data w :=
  measureFin (Fintype.card I) (fun i=>wire ((Fintype.equivFin I).symm i))
    (fun bs=>next (bs ∘ Fintype.equivFin I))

/-- A measured wire receives either no gate or its literal X gate. -/
def feedback (Etarget observed : State Aux Data) : List (Wire Aux Data) →
    Program G A B Aux Data w → Program G A B Aux Data w
  | [], next => next
  | i::wires, next => feedback Etarget observed wires
      (if resetWord Etarget wires observed i = Etarget i then next else .bitX i next)

def reset (target observed : State Aux Data) (next : Program G A B Aux Data w) :=
  feedback target observed Finset.univ.toList next

theorem cost_measureFin (k : ℕ) (wire : Fin k → Wire Aux Data)
    (next : (Fin k → Bool) → Program G A B Aux Data w) (N : ℕ)
    (hn : ∀ bs, (next bs).cost ≤ N) : (measureFin k wire next).cost ≤ k+N := by
  induction k with
  | zero => simpa [measureFin] using hn Fin.elim0
  | succ k ih =>
    simp only [measureFin,cost]
    have hf := ih (fun i=>wire i.succ) (fun bs=>next (Fin.cons false bs)) (fun bs=>hn _)
    have ht := ih (fun i=>wire i.succ) (fun bs=>next (Fin.cons true bs)) (fun bs=>hn _)
    omega

theorem cost_measureAll {I : Type*} [Fintype I] (wire : I → Wire Aux Data)
    (next : (I → Bool) → Program G A B Aux Data w) (N : ℕ)
    (hn : ∀ bs, (next bs).cost ≤ N) : (measureAll wire next).cost ≤ Fintype.card I+N :=
  cost_measureFin _ _ _ N (fun _=>hn _)

theorem cost_feedback (target observed : State Aux Data) (wires : List (Wire Aux Data))
    (next : Program G A B Aux Data w) :
    (feedback target observed wires next).cost ≤ wires.length + next.cost := by
  induction wires generalizing next with
  | nil => simp [feedback]
  | cons i wires ih =>
    simp only [feedback]
    have h := ih (if resetWord target wires observed i = target i then next else .bitX i next)
    by_cases hh : resetWord target wires observed i = target i
    · simp only [if_pos hh] at h ⊢
      exact h.trans (by simp)
    · simp only [if_neg hh,cost,List.length_cons] at h ⊢
      omega

theorem cost_reset (target observed : State Aux Data) (next : Program G A B Aux Data w) :
    (reset target observed next).cost ≤ Fintype.card (Wire Aux Data)+next.cost := by
  simpa [reset] using cost_feedback target observed Finset.univ.toList next

end Program
end OptimalQLS.Refinement.CostedExecution
