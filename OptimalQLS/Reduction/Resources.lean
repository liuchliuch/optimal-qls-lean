import OptimalQLS.Reduction.Repetition

/-! Resources of the same finite reset/extraction program. Instrument depth is
reported as instrument depth, never as an elementary-unitary-gate count. -/
noncomputable section
open scoped BigOperators
namespace OptimalQLS.Reduction
open Matrix LowerBounds Refinement.Repetition
set_option maxHeartbeats 500000
universe u v
variable {A : Type u} {B : Type v} {d m w : ℕ}

theorem bindOutput_matrixDepth (tree : FiniteOracleProgram A B m w)
    (next : Bool → FiniteOracleProgram A B d m) (M : ℕ)
    (h : ∀ flag, matrixDepth (next flag) ≤ M) :
    matrixDepth (bindOutput tree next) ≤ matrixDepth tree + M := by
  induction tree with
  | output flag aborted => simpa [bindOutput, matrixDepth] using h flag
  | matrixQuery p adj tree ih => simpa [bindOutput, matrixDepth, Nat.add_right_comm] using Nat.add_le_add_right ih 1
  | vectorQuery p adj tree ih => exact ih
  | instrument r dims K hn tree ih =>
    apply Finset.sup_le
    intro i _
    exact (ih i).trans (Nat.add_le_add_right (Finset.le_sup (f := fun j => matrixDepth (tree j)) (Finset.mem_univ i)) M)

theorem bindOutput_instrumentDepth (tree : FiniteOracleProgram A B m w)
    (next : Bool → FiniteOracleProgram A B d m) (M : ℕ)
    (h : ∀ flag, instrumentDepth (next flag) ≤ M) :
    instrumentDepth (bindOutput tree next) ≤ instrumentDepth tree + M := by
  induction tree with
  | output flag aborted => simpa [bindOutput, instrumentDepth] using h flag
  | matrixQuery p adj tree ih => exact ih
  | vectorQuery p adj tree ih => exact ih
  | instrument r dims K hn tree ih =>
    have hsup : (Finset.univ.sup fun i => instrumentDepth (bindOutput (tree i) next)) ≤
        (Finset.univ.sup fun i => instrumentDepth (tree i)) + M := by
      apply Finset.sup_le
      intro i _
      exact (ih i).trans (Nat.add_le_add_right (Finset.le_sup (f := fun j => instrumentDepth (tree j)) (Finset.mem_univ i)) M)
    simpa [bindOutput, instrumentDepth, Nat.add_right_comm] using Nat.add_le_add_right hsup 1

theorem bindOutput_registerBound (tree : FiniteOracleProgram A B m w)
    (next : Bool → FiniteOracleProgram A B d m) (M : ℕ)
    (ht : RegisterBound M tree) (hn : ∀ flag, RegisterBound M (next flag)) :
    RegisterBound M (bindOutput tree next) := by
  induction tree with
  | output flag aborted => exact hn flag
  | matrixQuery p adj tree ih => exact ⟨ht.1,ih ht.2⟩
  | vectorQuery p adj tree ih => exact ⟨ht.1,ih ht.2⟩
  | instrument r dims K hc tree ih => exact ⟨ht.1,fun i => ih i (ht.2 i)⟩

theorem retrySolver_matrixDepth (tree : FiniteOracleProgram A B m w)
    (e : Fin d ↪ Fin m) (zero : Fin w) (out : Fin d) (n : ℕ) :
    matrixDepth (retrySolver tree e zero out n) ≤ n * matrixDepth tree := by
  induction n with
  | zero => simp [retrySolver, failureOutput, matrixDepth]
  | succ n ih =>
    have h := bindOutput_matrixDepth tree
      (fun flag => if flag then measureExtract e zero out (retrySolver tree e zero out n)
        else measuredReset zero (retrySolver tree e zero out n)) (n * matrixDepth tree) (by
          intro flag
          cases flag <;> simp only [Bool.false_eq_true, ite_false, ite_true,
            measuredReset, measureExtract, matrixDepth]
          · exact Finset.sup_le (fun _ _ => ih)
          · apply Finset.sup_le
            intro i _
            refine Fin.cases (Nat.zero_le _) (fun _ => ?_) i
            exact Finset.sup_le (fun _ _ => ih))
    simpa [retrySolver, extractAndRetry, Nat.add_mul, Nat.add_comm] using h

theorem retrySolver_instrumentDepth (tree : FiniteOracleProgram A B m w)
    (e : Fin d ↪ Fin m) (zero : Fin w) (out : Fin d) (n : ℕ) :
    instrumentDepth (retrySolver tree e zero out n) ≤ n * (instrumentDepth tree + 2) + 1 := by
  induction n with
  | zero => simp [retrySolver, failureOutput, instrumentDepth]
  | succ n ih =>
    have hnext : ∀ flag, instrumentDepth
      ((fun flag : Bool => if flag then measureExtract e zero out (retrySolver tree e zero out n)
        else measuredReset zero (retrySolver tree e zero out n)) flag) ≤
          n * (instrumentDepth tree + 2) + 3 := by
      intro flag
      have hr : instrumentDepth (measuredReset (m := m) zero (retrySolver tree e zero out n)) ≤
          n * (instrumentDepth tree + 2) + 2 := by
        change (Finset.univ.sup fun _ : Fin m => instrumentDepth (retrySolver tree e zero out n)) + 1 ≤ _
        have hs := Finset.sup_le (s := (Finset.univ : Finset (Fin m))) (fun _ _ => ih)
        omega
      cases flag
      · exact hr.trans (by omega)
      · change (Finset.univ.sup fun i : Fin (m+1) => instrumentDepth
          (Fin.cases (motive := fun j => FiniteOracleProgram A B d (nextDimension d m j))
            (.output true false) (fun _ => measuredReset zero (retrySolver tree e zero out n)) i)) + 1 ≤ _
        have hs : (Finset.univ.sup fun i : Fin (m+1) => instrumentDepth
          (Fin.cases (motive := fun j => FiniteOracleProgram A B d (nextDimension d m j))
            (.output true false) (fun _ => measuredReset zero (retrySolver tree e zero out n)) i)) ≤
              n * (instrumentDepth tree + 2) + 2 := by
          apply Finset.sup_le
          intro i _
          exact Fin.cases (Nat.zero_le _) (fun _ => hr) i
        omega
    have h := bindOutput_instrumentDepth tree _ _ hnext
    change instrumentDepth (bindOutput tree _) ≤ _
    simp only [Nat.add_mul, Nat.one_mul]
    omega

theorem retrySolver_registerBound (tree : FiniteOracleProgram A B m w)
    (e : Fin d ↪ Fin m) (zero : Fin w) (out : Fin d) (n M : ℕ)
    (ht : RegisterBound M tree) (hw : w ≤ M) (hm : m ≤ M) :
    RegisterBound M (retrySolver tree e zero out n) := by
  have hd : d ≤ M := (show d ≤ m by
    simpa using Fintype.card_le_of_injective e e.injective).trans hm
  induction n with
  | zero => exact ⟨hw,fun _ => hd⟩
  | succ n ih =>
    apply bindOutput_registerBound tree _ M ht
    intro flag
    have hr : RegisterBound M (measuredReset (m := m) zero (retrySolver tree e zero out n)) :=
      ⟨hm,fun _ => ih⟩
    cases flag
    · exact hr
    · refine ⟨hm,?_⟩
      intro i
      exact Fin.cases hd (fun _ => hr) i

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

theorem bindOutput_vectorDepth (tree : FiniteOracleProgram A B m w)
    (next : Bool → FiniteOracleProgram A B d m) (M : ℕ)
    (h : ∀ flag, (next flag).vectorDepth ≤ M) :
    (bindOutput tree next).vectorDepth ≤ tree.vectorDepth + M := by
  induction tree with
  | output flag aborted => simpa [bindOutput, FiniteOracleProgram.vectorDepth] using h flag
  | matrixQuery p adj tree ih => exact ih
  | vectorQuery p adj tree ih => simpa [bindOutput, FiniteOracleProgram.vectorDepth, Nat.add_right_comm] using Nat.add_le_add_right ih 1
  | instrument r dims K hn tree ih =>
    apply Finset.sup_le
    intro i _
    exact (ih i).trans (Nat.add_le_add_right (Finset.le_sup (f := fun j => (tree j).vectorDepth) (Finset.mem_univ i)) M)

theorem retrySolver_vectorDepth (tree : FiniteOracleProgram A B m w)
    (e : Fin d ↪ Fin m) (zero : Fin w) (out : Fin d) (n : ℕ) :
    (retrySolver tree e zero out n).vectorDepth ≤ n * tree.vectorDepth := by
  induction n with
  | zero => simp [retrySolver, failureOutput, FiniteOracleProgram.vectorDepth]
  | succ n ih =>
    have h := bindOutput_vectorDepth tree
      (fun flag => if flag then measureExtract e zero out (retrySolver tree e zero out n)
        else measuredReset zero (retrySolver tree e zero out n)) (n * tree.vectorDepth) (by
          intro flag
          cases flag <;> simp only [Bool.false_eq_true, ite_false, ite_true,
            measuredReset, measureExtract, FiniteOracleProgram.vectorDepth]
          · exact Finset.sup_le (fun _ _ => ih)
          · apply Finset.sup_le
            intro i _
            refine Fin.cases (Nat.zero_le _) (fun _ => ?_) i
            exact Finset.sup_le (fun _ _ => ih))
    simpa [retrySolver, extractAndRetry, Nat.add_mul, Nat.add_comm] using h

end OptimalQLS.Reduction
