import OptimalQLS.LowerBounds.BranchIsometryNorm

/-!
# Oracle hybrid for a single actual varying-workspace instruction tree

This is a coherent Stinespring estimate derived from the terminal Kraus
matrices. Measurement branches and their individual adjoint choices are part
of the same syntax. No separately assumed representation or hybrid is used.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix QuantumChannelStein.TraceNorm
universe u v
variable {A : Type u} {B : Type v} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  {d w : ℕ}

def FiniteOracleProgram.vectorDepth : {w : ℕ} → FiniteOracleProgram A B d w → ℕ
  | _, .output _ _ => 0
  | _, .matrixQuery _ _ next => next.vectorDepth
  | _, .vectorQuery _ _ next => next.vectorDepth + 1
  | _, .instrument _ _ _ _ next => Finset.univ.sup (fun i => (next i).vectorDepth)

theorem FiniteOracleProgram.terminalIsometry_matrixQuery (port : OptimalQLS.QueryPort A (Fin w))
    (adj : Bool) (next : FiniteOracleProgram A B d w) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (FiniteOracleProgram.matrixQuery port adj next).terminalIsometry UA Ub =
      next.terminalIsometry UA Ub * (port.apply (if adj then UA⁻¹ else UA) : Matrix (Fin w) (Fin w) ℂ) := by
  ext i j
  rfl

theorem FiniteOracleProgram.terminalIsometry_vectorQuery (port : OptimalQLS.QueryPort B (Fin w))
    (adj : Bool) (next : FiniteOracleProgram A B d w) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (FiniteOracleProgram.vectorQuery port adj next).terminalIsometry UA Ub =
      next.terminalIsometry UA Ub * (port.apply (if adj then Ub⁻¹ else Ub) : Matrix (Fin w) (Fin w) ℂ) := by
  ext i j
  rfl

/-- Coherent norm difference is at most maximum vector-query depth times the
full oracle distance, proved by induction on the actual program. -/
theorem FiniteOracleProgram.terminalIsometry_vector_hybrid (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (U V : Matrix.unitaryGroup B ℂ) :
    ‖tree.terminalIsometry UA U - tree.terminalIsometry UA V‖ ≤
      (tree.vectorDepth : ℝ) * ‖(U : Matrix B B ℂ) - (V : Matrix B B ℂ)‖ := by
  classical
  let delta := ‖(U : Matrix B B ℂ) - (V : Matrix B B ℂ)‖
  have hd : 0 ≤ delta := norm_nonneg _
  induction tree with
  | output flag aborted =>
    have heq : (FiniteOracleProgram.output (A := A) (B := B) (d := d) flag aborted).terminalIsometry UA U =
        (FiniteOracleProgram.output (A := A) (B := B) (d := d) flag aborted).terminalIsometry UA V := by ext i j; rfl
    rw [heq, sub_self, norm_zero]
    simp [vectorDepth]
  | @matrixQuery ww port adj next ih =>
    rw [terminalIsometry_matrixQuery, terminalIsometry_matrixQuery, ← Matrix.sub_mul]
    apply (Matrix.l2_opNorm_mul _ _).trans
    exact (mul_le_of_le_one_right (norm_nonneg _)
      (unitary_opNorm_le_one (port.apply (if adj then UA⁻¹ else UA)))).trans ih
  | @vectorQuery ww port adj next ih =>
    let QU : Matrix (Fin ww) (Fin ww) ℂ := port.apply (if adj then U⁻¹ else U)
    let QV : Matrix (Fin ww) (Fin ww) ℂ := port.apply (if adj then V⁻¹ else V)
    rw [terminalIsometry_vectorQuery, terminalIsometry_vectorQuery]
    have heq : next.terminalIsometry UA U * QU - next.terminalIsometry UA V * QV =
        (next.terminalIsometry UA U - next.terminalIsometry UA V) * QU +
          next.terminalIsometry UA V * (QU - QV) := by rw [Matrix.sub_mul, Matrix.mul_sub]; abel
    change ‖next.terminalIsometry UA U * QU - next.terminalIsometry UA V * QV‖ ≤ _
    rw [heq]
    have h₁ : ‖(next.terminalIsometry UA U - next.terminalIsometry UA V) * QU‖ ≤ (next.vectorDepth : ℝ) * delta :=
      (Matrix.l2_opNorm_mul _ _).trans ((mul_le_of_le_one_right (norm_nonneg _)
        (unitary_opNorm_le_one (port.apply (if adj then U⁻¹ else U)))).trans ih)
    have h₂ : ‖next.terminalIsometry UA V * (QU - QV)‖ ≤ delta :=
      (Matrix.l2_opNorm_mul _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) (next.terminalIsometry_norm_le_one UA V)).trans
        (queryPort_adjoint_difference_norm_le port adj U V))
    have hsum := (norm_add_le _ _).trans (add_le_add h₁ h₂)
    simpa only [vectorDepth, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hsum
  | @instrument ww r dims K hn next ih =>
    have heq : (FiniteOracleProgram.instrument r dims K hn next).terminalIsometry UA U -
        (FiniteOracleProgram.instrument r dims K hn next).terminalIsometry UA V =
        branchComposition dims (fun i => (next i).terminalIsometry UA U - (next i).terminalIsometry UA V) K := by
      ext row col
      simp [terminalIsometry, terminalKraus, branchComposition, Matrix.sub_mul, Matrix.mul_apply, sub_mul, Finset.sum_sub_distrib]
    rw [heq]
    apply branchComposition_norm_le dims _ K hn _ (by positivity)
    intro i
    apply (ih i).trans
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.le_sup (f := fun i => (next i).vectorDepth) (Finset.mem_univ i)) hd

end OptimalQLS.LowerBounds
