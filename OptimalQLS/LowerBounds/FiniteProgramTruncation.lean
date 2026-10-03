import OptimalQLS.LowerBounds.FiniteProgramHybrid

/-!
# Actual vector-query truncation of the common instruction tree

Aborting measures the current finite basis and prepares a fixed output basis
state with its separate abort tag. The resulting operation is a literal
normalized instrument. Cutoff mass is the actual Born mass reaching cuts.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
universe u v
variable {A : Type u} {B : Type v} {d w : ℕ}

def abortBasisKraus (out : Fin d) (j : Fin w) : Matrix (Fin d) (Fin w) ℂ :=
  fun i k => if i = out then if k = j then 1 else 0 else 0

theorem abortBasisKraus_normalized (out : Fin d) :
    (∑ j : Fin w, (abortBasisKraus out j).conjTranspose * abortBasisKraus out j) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [abortBasisKraus, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply]
  · simp [abortBasisKraus, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, hij, Ne.symm hij]

def FiniteOracleProgram.abortProgram (out : Fin d) (w : ℕ) : FiniteOracleProgram A B d w :=
  .instrument w (fun _ => d) (abortBasisKraus out) (abortBasisKraus_normalized out) (fun _ => .output false true)

@[simp] theorem FiniteOracleProgram.abortProgram_vectorDepth (out : Fin d) (w : ℕ) :
    (abortProgram (A := A) (B := B) out w).vectorDepth = 0 := by
  simp [abortProgram, vectorDepth]

def FiniteOracleProgram.truncateVectors (out : Fin d) :
    (q : ℕ) → {w : ℕ} → FiniteOracleProgram A B d w → FiniteOracleProgram A B d w
  | _, _, .output success aborted => .output success aborted
  | q, _, .matrixQuery port adj next => .matrixQuery port adj (next.truncateVectors out q)
  | 0, w, .vectorQuery _ _ _ => abortProgram out w
  | q + 1, _, .vectorQuery port adj next => .vectorQuery port adj (next.truncateVectors out q)
  | q, _, .instrument r dims K hn next => .instrument r dims K hn (fun i => (next i).truncateVectors out q)

theorem FiniteOracleProgram.truncateVectors_depth (tree : FiniteOracleProgram A B d w) (out : Fin d) (q : ℕ) :
    (tree.truncateVectors out q).vectorDepth ≤ q := by
  induction tree generalizing q with
  | output success aborted => simp [truncateVectors, vectorDepth]
  | matrixQuery port adj next ih => exact ih q
  | vectorQuery port adj next ih =>
    cases q with
    | zero => simp [truncateVectors]
    | succ q => exact Nat.succ_le_succ (ih q)
  | instrument r dims K hn next ih =>
    change Finset.univ.sup (fun i => ((next i).truncateVectors out q).vectorDepth) ≤ q
    exact Finset.sup_le (fun i _ => ih i q)

def FiniteOracleProgram.terminalVectorQueries : {w : ℕ} → (tree : FiniteOracleProgram A B d w) → tree.Terminal → ℕ
  | _, .output _ _ => fun _ => 0
  | _, .matrixQuery _ _ next => next.terminalVectorQueries
  | _, .vectorQuery _ _ next => fun k => next.terminalVectorQueries k + 1
  | _, .instrument _ _ _ _ next => fun k => (next k.1).terminalVectorQueries k.2

theorem FiniteOracleProgram.terminalPath_vectorQueries (tree : FiniteOracleProgram A B d w)
    (path : VariableQueryPath A B w) (k : tree.Terminal) :
    (tree.terminalPath path k).vectorQueries = path.vectorQueries + tree.terminalVectorQueries k := by
  induction tree with
  | output success aborted => simp [terminalPath, terminalVectorQueries]
  | matrixQuery port adj next ih => exact ih (.matrixQuery port adj path) k
  | vectorQuery port adj next ih =>
    have h := ih (.vectorQuery port adj path) k
    simpa only [terminalPath, VariableQueryPath.vectorQueries, terminalVectorQueries, Nat.add_assoc,
      Nat.add_comm 1 (next.terminalVectorQueries k)] using h
  | instrument r dims K hn next ih => exact ih k.1 (.work (K k.1) path) k.2

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def FiniteOracleProgram.terminalBorn (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) (k : tree.Terminal) : ℝ :=
  bornMass (tree.terminalKraus UA Ub k *ᵥ psi)

theorem FiniteOracleProgram.terminalBorn_total (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) :
    (∑ k : tree.Terminal, tree.terminalBorn UA Ub psi k) = bornMass psi := by
  rw [← tree.terminalBorn_sum UA Ub psi]
  apply Finset.sum_congr rfl
  intro k _
  have h := tree.terminalKraus_path_state (.initial psi) UA Ub k
  change tree.terminalKraus UA Ub k *ᵥ psi = _ at h
  rw [terminalBorn, h]
  rfl

def FiniteOracleProgram.PointwiseVectorBound (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ) (q : ℕ) : Prop :=
  ∀ k, 0 < tree.terminalBorn UA Ub psi k → tree.terminalVectorQueries k ≤ q

def FiniteOracleProgram.cutMass (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (q : ℕ) → {w : ℕ} → FiniteOracleProgram A B d w → (Fin w → ℂ) → ℝ
  | _, _, .output _ _, _ => 0
  | q, w, .matrixQuery port adj next, psi => next.cutMass UA Ub q
      ((port.apply (if adj then UA⁻¹ else UA) : Matrix (Fin w) (Fin w) ℂ) *ᵥ psi)
  | 0, _, .vectorQuery _ _ _, psi => bornMass psi
  | q + 1, w, .vectorQuery port adj next, psi => next.cutMass UA Ub q
      ((port.apply (if adj then Ub⁻¹ else Ub) : Matrix (Fin w) (Fin w) ℂ) *ᵥ psi)
  | q, _, .instrument _ _ K _ next, psi => ∑ i, (next i).cutMass UA Ub q (K i *ᵥ psi)

/-- An original-input bound on positive terminal Born runs makes the actual
truncation cut mass vanish. Dead syntactic long branches do not count. -/
theorem FiniteOracleProgram.cutMass_zero_of_pointwise_bound (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (psi : Fin w → ℂ)
    (q : ℕ) (hq : tree.PointwiseVectorBound UA Ub psi q) : tree.cutMass UA Ub q psi = 0 := by
  induction tree generalizing q with
  | output success aborted => rfl
  | matrixQuery port adj next ih =>
    apply ih _ q
    intro k hk
    apply hq k
    simpa only [terminalBorn, terminalKraus, ← Matrix.mulVec_mulVec] using hk
  | vectorQuery port adj next ih =>
    cases q with
    | zero =>
      change bornMass psi = 0
      rw [← (FiniteOracleProgram.vectorQuery port adj next).terminalBorn_total UA Ub psi]
      apply Finset.sum_eq_zero
      intro k _
      apply le_antisymm _ (by
        unfold terminalBorn bornMass
        exact Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _))
      apply le_of_not_gt
      intro hk
      have h := hq k hk
      change next.terminalVectorQueries k + 1 ≤ 0 at h
      omega
    | succ q =>
      apply ih _ q
      intro k hk
      have hp : 0 < (FiniteOracleProgram.vectorQuery port adj next).terminalBorn UA Ub psi k := by
        simpa only [terminalBorn, terminalKraus, ← Matrix.mulVec_mulVec] using hk
      have h := hq k hp
      change next.terminalVectorQueries k + 1 ≤ q + 1 at h
      omega
  | instrument r dims K hn next ih =>
    change (∑ i, (next i).cutMass UA Ub q (K i *ᵥ psi)) = 0
    apply Finset.sum_eq_zero
    intro i _
    apply ih i _ q
    intro k hk
    apply hq ⟨i, k⟩
    simpa only [terminalBorn, terminalKraus, ← Matrix.mulVec_mulVec] using hk

end OptimalQLS.LowerBounds
