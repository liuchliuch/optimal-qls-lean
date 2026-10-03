import OptimalQLS.LowerBounds.FiniteProgramKraus
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! Concrete flagged readout channel of the common instruction tree. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
universe u v
variable {A : Type u} {B : Type v} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  {d w : ℕ}

noncomputable instance FiniteOracleProgram.terminalDecidableEq (tree : FiniteOracleProgram A B d w) :
    DecidableEq tree.Terminal := Classical.decEq _

def flagInjection (flag : Bool) : Matrix (Fin d ⊕ Fin d) (Fin d) ℂ :=
  if flag then Matrix.fromRows 1 0 else Matrix.fromRows 0 1

theorem flagInjection_gram (flag : Bool) : (flagInjection (d := d) flag).conjTranspose * flagInjection (d := d) flag = 1 := by
  cases flag <;> simp [flagInjection, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromRows]

def terminalProjection {T : Type*} [DecidableEq T] (k : T) : Matrix (Fin d) (T × Fin d) ℂ :=
  fun i j => if k = j.1 then if i = j.2 then 1 else 0 else 0

theorem terminalProjection_normalized {T : Type*} [Fintype T] [DecidableEq T] :
    (∑ k : T, (terminalProjection (d := d) k).conjTranspose * terminalProjection k) = 1 := by
  ext a b
  rcases a with ⟨a, i⟩
  rcases b with ⟨b, j⟩
  by_cases hab : a = b
  · subst b
    by_cases hij : i = j
    · subst j
      simp [terminalProjection, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply]
    · simp [terminalProjection, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, hij, Ne.symm hij]
  · simp [terminalProjection, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, hab, Ne.symm hab]

def FiniteOracleProgram.readoutKraus (tree : FiniteOracleProgram A B d w) :
    tree.Terminal → Matrix (Fin d ⊕ Fin d) (tree.Terminal × Fin d) ℂ := by
  classical
  exact fun k => flagInjection (tree.terminalSuccess k) * terminalProjection k

theorem FiniteOracleProgram.readoutKraus_normalized (tree : FiniteOracleProgram A B d w) :
    (∑ k, (tree.readoutKraus k).conjTranspose * tree.readoutKraus k) = 1 := by
  classical
  calc
    _ = ∑ k : tree.Terminal, (terminalProjection k).conjTranspose * terminalProjection (d := d) k := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [readoutKraus, Matrix.conjTranspose_mul]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (flagInjection (tree.terminalSuccess k)).conjTranspose,
        flagInjection_gram, Matrix.one_mul]
    _ = 1 := terminalProjection_normalized

def FiniteOracleProgram.readoutChannel (tree : FiniteOracleProgram A B d w) :
    FiniteChannel (tree.Terminal × Fin d) (Fin d ⊕ Fin d) := by
  classical
  exact FiniteChannel.ofKraus tree.readoutKraus tree.readoutKraus_normalized

def FiniteOracleProgram.outputKraus (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (k : tree.Terminal) :
    Matrix (Fin d ⊕ Fin d) (Fin w) ℂ := flagInjection (tree.terminalSuccess k) * tree.terminalKraus UA Ub k

theorem FiniteOracleProgram.outputKraus_normalized (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (∑ k, (tree.outputKraus UA Ub k).conjTranspose * tree.outputKraus UA Ub k) = 1 := by
  calc
    _ = ∑ k, (tree.terminalKraus UA Ub k).conjTranspose * tree.terminalKraus UA Ub k := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [outputKraus, Matrix.conjTranspose_mul]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (flagInjection (tree.terminalSuccess k)).conjTranspose,
        flagInjection_gram, Matrix.one_mul]
    _ = 1 := tree.terminalKraus_normalized UA Ub

def FiniteOracleProgram.outputChannel (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) : FiniteChannel (Fin w) (Fin d ⊕ Fin d) :=
  FiniteChannel.ofKraus (tree.outputKraus UA Ub) (tree.outputKraus_normalized UA Ub)

theorem FiniteOracleProgram.project_terminalIsometry (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (k : tree.Terminal) :
    tree.readoutKraus k * tree.terminalIsometry UA Ub = tree.outputKraus UA Ub k := by
  classical
  have hp : terminalProjection k * tree.terminalIsometry UA Ub = tree.terminalKraus UA Ub k := by
    ext i j
    simp [terminalProjection, terminalIsometry, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [readoutKraus, Matrix.mul_assoc, hp]
  rfl

/-- Actual channel output equals the fixed readout applied to the actual
terminal Stinespring matrix, for every input density matrix. -/
theorem FiniteOracleProgram.outputChannel_stinespring (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) (X : Matrix (Fin w) (Fin w) ℂ) :
    (tree.outputChannel UA Ub).apply X = tree.readoutChannel.apply
      (tree.terminalIsometry UA Ub * X * (tree.terminalIsometry UA Ub).conjTranspose) := by
  classical
  rw [outputChannel, readoutChannel, FiniteChannel.ofKraus_apply, FiniteChannel.ofKraus_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [← tree.project_terminalIsometry UA Ub k, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

end OptimalQLS.LowerBounds
