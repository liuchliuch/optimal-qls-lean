import OptimalQLS.Refinement.Repetition.Program

/-! Worst-case resources extracted from the actual recursive program.
Every instrument, including measurement/reset and final failure output, is
charged. Matrix-work depth is deliberately not called elementary-gate count. -/
noncomputable section
open scoped BigOperators
namespace OptimalQLS.Refinement.Repetition
open Matrix LowerBounds
set_option maxHeartbeats 500000
universe u v
variable {A : Type u} {B : Type v} {d w : ℕ}

def matrixDepth : {w : ℕ} → FiniteOracleProgram A B d w → ℕ
  | _, .output _ _ => 0
  | _, .matrixQuery _ _ next => matrixDepth next + 1
  | _, .vectorQuery _ _ next => matrixDepth next
  | _, .instrument _ _ _ _ next => Finset.univ.sup (fun i => matrixDepth (next i))

def instrumentDepth : {w : ℕ} → FiniteOracleProgram A B d w → ℕ
  | _, .output _ _ => 0
  | _, .matrixQuery _ _ next => instrumentDepth next
  | _, .vectorQuery _ _ next => instrumentDepth next
  | _, .instrument _ _ _ _ next => Finset.univ.sup (fun i => instrumentDepth (next i)) + 1

def workCount : QueryCircuit A B (Fin w) → ℕ
  | [] => 0
  | .work _ :: c => workCount c + 1
  | _ :: c => workCount c

/-- Every live quantum register has dimension at most M. Classical branches
are not retained as coherent quantum history registers. -/
def RegisterBound (M : ℕ) : {w : ℕ} → FiniteOracleProgram A B d w → Prop
  | _, .output _ _ => d ≤ M
  | w, .matrixQuery _ _ next => w ≤ M ∧ RegisterBound M next
  | w, .vectorQuery _ _ next => w ≤ M ∧ RegisterBound M next
  | w, .instrument _ _ _ _ next => w ≤ M ∧ ∀ i, RegisterBound M (next i)

theorem prepend_matrixDepth (c : QueryCircuit A B (Fin w)) (next : FiniteOracleProgram A B d w) :
    matrixDepth (prepend c next) = c.matrixQueries + matrixDepth next := by
  induction c with
  | nil => simp [prepend, QueryCircuit.matrixQueries]
  | cons gate c ih => cases gate <;> simp [prepend, matrixDepth, ih, QueryCircuit.matrixQueries, Nat.add_right_comm]

theorem prepend_instrumentDepth (c : QueryCircuit A B (Fin w)) (next : FiniteOracleProgram A B d w) :
    instrumentDepth (prepend c next) = workCount c + instrumentDepth next := by
  induction c with
  | nil => simp [prepend, workCount]
  | cons gate c ih => cases gate <;> simp [prepend, instrumentDepth, ih, workCount, Nat.add_right_comm]

theorem prepend_registerBound (c : QueryCircuit A B (Fin w)) (next : FiniteOracleProgram A B d w)
    (M : ℕ) (hw : w ≤ M) (hn : RegisterBound M next) : RegisterBound M (prepend c next) := by
  induction c with
  | nil => exact hn
  | cons gate c ih => cases gate <;> simp [prepend, RegisterBound, hw, ih]

theorem repeatProgram_matrixDepth (c : QueryCircuit A B (Fin w)) (e : Fin d ↪ Fin w)
    (zero : Fin w) (out : Fin d) (n : ℕ) :
    matrixDepth (repeatProgram c e zero out n) ≤ n * c.matrixQueries := by
  induction n with
  | zero => simp [repeatProgram, failureOutput, matrixDepth]
  | succ n ih =>
    rw [repeatProgram, prepend_matrixDepth]
    have h : matrixDepth (FiniteOracleProgram.instrument (w + 1) (nextDimension d w)
        (measurementKraus e zero) (measurementKraus_complete e zero)
        (Fin.cases (.output true false) (fun _ => repeatProgram c e zero out n))) ≤ n * c.matrixQueries := by
      apply Finset.sup_le
      intro i _
      refine Fin.cases ?_ (fun _ => ih) i
      exact Nat.zero_le _
    exact (Nat.add_le_add_left h _).trans_eq (by simp [Nat.add_mul, Nat.add_comm])

theorem repeatProgram_instrumentDepth (c : QueryCircuit A B (Fin w)) (e : Fin d ↪ Fin w)
    (zero : Fin w) (out : Fin d) (n : ℕ) :
    instrumentDepth (repeatProgram c e zero out n) ≤ n * (workCount c + 1) + 1 := by
  induction n with
  | zero => simp [repeatProgram, failureOutput, instrumentDepth]
  | succ n ih =>
    rw [repeatProgram, prepend_instrumentDepth]
    have h : (Finset.univ.sup (fun i : Fin (w + 1) => instrumentDepth
        (Fin.cases (motive := fun j => FiniteOracleProgram A B d (nextDimension d w j))
          (FiniteOracleProgram.output true false) (fun _ => repeatProgram c e zero out n) i))) ≤ n * (workCount c + 1) + 1 := by
      apply Finset.sup_le
      intro i _
      refine Fin.cases ?_ (fun _ => ih) i
      exact Nat.zero_le _
    change workCount c + (_ + 1) ≤ _
    simp only [Nat.add_mul, Nat.one_mul]
    omega

theorem repeatProgram_registerBound (c : QueryCircuit A B (Fin w)) (e : Fin d ↪ Fin w)
    (zero : Fin w) (out : Fin d) (n : ℕ) :
    RegisterBound w (repeatProgram c e zero out n) := by
  have hd : d ≤ w := by
    simpa using Fintype.card_le_of_injective e e.injective
  induction n with
  | zero => simp [repeatProgram, failureOutput, RegisterBound, hd]
  | succ n ih =>
    apply prepend_registerBound _ _ w le_rfl
    refine ⟨le_rfl, ?_⟩
    intro i
    exact Fin.cases hd (fun _ => ih) i

theorem terminalPath_matrixQueries_le (tree : FiniteOracleProgram A B d w)
    (path : VariableQueryPath A B w) (k : tree.Terminal) :
    (tree.terminalPath path k).matrixQueries ≤ path.matrixQueries + matrixDepth tree := by
  induction tree with
  | output flag aborted => simp [FiniteOracleProgram.terminalPath, matrixDepth]
  | matrixQuery port adj next ih =>
    have h := ih (.matrixQuery port adj path) k
    simpa only [FiniteOracleProgram.terminalPath, matrixDepth,
      VariableQueryPath.matrixQueries, Nat.add_right_comm, Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using h
  | vectorQuery port adj next ih => exact ih (.vectorQuery port adj path) k
  | instrument r dims K hn next ih =>
    have h := ih k.1 (.work (K k.1) path) k.2
    exact h.trans (Nat.add_le_add_left (Finset.le_sup (f := fun i => matrixDepth (next i)) (Finset.mem_univ k.1)) _)

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

theorem prepend_vectorDepth (c : QueryCircuit A B (Fin w)) (next : FiniteOracleProgram A B d w) :
    (prepend c next).vectorDepth = c.vectorQueries + next.vectorDepth := by
  induction c with
  | nil => simp [prepend, QueryCircuit.vectorQueries]
  | cons gate c ih => cases gate <;> simp [prepend, FiniteOracleProgram.vectorDepth, ih, QueryCircuit.vectorQueries, Nat.add_right_comm]

theorem repeatProgram_vectorDepth (c : QueryCircuit A B (Fin w)) (e : Fin d ↪ Fin w)
    (zero : Fin w) (out : Fin d) (n : ℕ) :
    (repeatProgram c e zero out n).vectorDepth ≤ n * c.vectorQueries := by
  induction n with
  | zero => simp [repeatProgram, failureOutput, FiniteOracleProgram.vectorDepth]
  | succ n ih =>
    rw [repeatProgram, prepend_vectorDepth]
    have h : (FiniteOracleProgram.instrument (w + 1) (nextDimension d w)
        (measurementKraus e zero) (measurementKraus_complete e zero)
        (Fin.cases (.output true false) (fun _ => repeatProgram c e zero out n))).vectorDepth ≤ n * c.vectorQueries := by
      apply Finset.sup_le
      intro i _
      refine Fin.cases ?_ (fun _ => ih) i
      exact Nat.zero_le _
    exact (Nat.add_le_add_left h _).trans_eq (by simp [Nat.add_mul, Nat.add_comm])


theorem terminalPath_vectorQueries_le (tree : FiniteOracleProgram A B d w)
    (path : VariableQueryPath A B w) (k : tree.Terminal) :
    (tree.terminalPath path k).vectorQueries ≤ path.vectorQueries + tree.vectorDepth := by
  induction tree with
  | output flag aborted => simp [FiniteOracleProgram.terminalPath, FiniteOracleProgram.vectorDepth]
  | matrixQuery port adj next ih => exact ih (.matrixQuery port adj path) k
  | vectorQuery port adj next ih =>
    have h := ih (.vectorQuery port adj path) k
    simpa only [FiniteOracleProgram.terminalPath, FiniteOracleProgram.vectorDepth,
      VariableQueryPath.vectorQueries, Nat.add_right_comm, Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using h
  | instrument r dims K hn next ih =>
    have h := ih k.1 (.work (K k.1) path) k.2
    exact h.trans (Nat.add_le_add_left (Finset.le_sup (f := fun i => (next i).vectorDepth) (Finset.mem_univ k.1)) _)

/-- Worst-case bounds hold for every syntactic terminal branch, not just
positive-probability runs and not merely on average. -/
theorem repeatProgram_terminal_queries (c : QueryCircuit A B (Fin w)) (e : Fin d ↪ Fin w)
    (zero : Fin w) (out : Fin d) (n : ℕ) (k : (repeatProgram c e zero out n).Terminal) :
    ((repeatProgram c e zero out n).terminalPath (.initial (basis zero)) k).matrixQueries ≤ n * c.matrixQueries ∧
    ((repeatProgram c e zero out n).terminalPath (.initial (basis zero)) k).vectorQueries ≤ n * c.vectorQueries := by
  constructor
  · exact (terminalPath_matrixQueries_le _ _ k).trans
      (by simpa [VariableQueryPath.matrixQueries] using repeatProgram_matrixDepth c e zero out n)
  · exact (terminalPath_vectorQueries_le _ _ k).trans
      (by simpa [VariableQueryPath.vectorQueries] using repeatProgram_vectorDepth c e zero out n)

end OptimalQLS.Refinement.Repetition
