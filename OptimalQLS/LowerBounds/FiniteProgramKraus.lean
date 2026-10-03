import OptimalQLS.LowerBounds.FiniteOracleProgram
import OptimalQLS.LowerBounds.TraceDistance

/-!
# Literal terminal Kraus matrices of the common instruction tree

Completeness is proved by structural recursion. The extracted matrices act
exactly like the extracted varying-workspace oracle paths, so the channel and
polynomial representations are derived from the same program.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
universe u v
variable {A : Type u} {B : Type v} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  {d w : ℕ}

lemma gram_sum_right_comp {I D E C : Type*} [Fintype I] [Fintype D] [Fintype E]
    (K : I → Matrix E D ℂ) (G : Matrix D C ℂ) :
    (∑ i, (K i * G).conjTranspose * (K i * G)) =
      G.conjTranspose * (∑ i, (K i).conjTranspose * K i) * G := by
  simp only [Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.mul_assoc]

def FiniteOracleProgram.terminalKraus (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    {w : ℕ} → (tree : FiniteOracleProgram A B d w) → tree.Terminal → Matrix (Fin d) (Fin w) ℂ
  | _, .output _ _, _ => 1
  | w, .matrixQuery port adj next, k => next.terminalKraus UA Ub k * (port.apply (if adj then UA⁻¹ else UA) : Matrix (Fin w) (Fin w) ℂ)
  | w, .vectorQuery port adj next, k => next.terminalKraus UA Ub k * (port.apply (if adj then Ub⁻¹ else Ub) : Matrix (Fin w) (Fin w) ℂ)
  | _, .instrument _ _ K _ next, k => (next k.1).terminalKraus UA Ub k.2 * K k.1

theorem FiniteOracleProgram.terminalKraus_normalized (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (∑ k : tree.Terminal, (tree.terminalKraus UA Ub k).conjTranspose * tree.terminalKraus UA Ub k) = 1 := by
  induction tree with
  | output flag aborted => simp [Terminal, terminalKraus]
  | @matrixQuery ww port adj next ih =>
    let Q : Matrix (Fin ww) (Fin ww) ℂ := port.apply (if adj then UA⁻¹ else UA)
    change (∑ k : next.Terminal, ((next.terminalKraus UA Ub k) * Q).conjTranspose * ((next.terminalKraus UA Ub k) * Q)) = 1
    rw [gram_sum_right_comp, ih, Matrix.mul_one]
    exact (port.apply (if adj then UA⁻¹ else UA)).property.1
  | @vectorQuery ww port adj next ih =>
    let Q : Matrix (Fin ww) (Fin ww) ℂ := port.apply (if adj then Ub⁻¹ else Ub)
    change (∑ k : next.Terminal, ((next.terminalKraus UA Ub k) * Q).conjTranspose * ((next.terminalKraus UA Ub k) * Q)) = 1
    rw [gram_sum_right_comp, ih, Matrix.mul_one]
    exact (port.apply (if adj then Ub⁻¹ else Ub)).property.1
  | instrument r dims K hn next ih =>
    change (∑ k : (i : Fin r) × (next i).Terminal,
      ((next k.1).terminalKraus UA Ub k.2 * K k.1).conjTranspose *
        ((next k.1).terminalKraus UA Ub k.2 * K k.1)) = _
    rw [Fintype.sum_sigma]
    calc
      _ = ∑ i, (K i).conjTranspose * K i := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only
        rw [gram_sum_right_comp, ih i, Matrix.mul_one]
      _ = 1 := hn

/-- Literal terminal matrices and actual typed oracle paths have equal states. -/
theorem FiniteOracleProgram.terminalKraus_path_state (tree : FiniteOracleProgram A B d w)
    (path : VariableQueryPath A B w) (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ)
    (k : tree.Terminal) :
    tree.terminalKraus UA Ub k *ᵥ path.state UA Ub = (tree.terminalPath path k).state UA Ub := by
  induction tree with
  | output flag aborted => simp [Terminal, terminalKraus, terminalPath]
  | matrixQuery port adj next ih =>
    rw [terminalKraus, ← Matrix.mulVec_mulVec]
    exact ih (.matrixQuery port adj path) k
  | vectorQuery port adj next ih =>
    rw [terminalKraus, ← Matrix.mulVec_mulVec]
    exact ih (.vectorQuery port adj path) k
  | instrument r dims K hn next ih =>
    rw [terminalKraus, ← Matrix.mulVec_mulVec]
    exact ih k.1 (.work (K k.1) path) k.2

/-- The coherent terminal matrix is constructed from all literal branch maps. -/
def FiniteOracleProgram.terminalIsometry (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) : Matrix (tree.Terminal × Fin d) (Fin w) ℂ :=
  fun i j => tree.terminalKraus UA Ub i.1 i.2 j

theorem FiniteOracleProgram.terminalIsometry_gram (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) :
    (tree.terminalIsometry UA Ub).conjTranspose * tree.terminalIsometry UA Ub = 1 := by
  ext i j
  have h := congrFun (congrFun (tree.terminalKraus_normalized UA Ub) i) j
  simpa [terminalIsometry, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, Fintype.sum_prod_type] using h

theorem FiniteOracleProgram.terminalIsometry_norm_le_one (tree : FiniteOracleProgram A B d w)
    (UA : Matrix.unitaryGroup A ℂ) (Ub : Matrix.unitaryGroup B ℂ) : ‖tree.terminalIsometry UA Ub‖ ≤ 1 := by
  classical
  exact matrix_isometry_norm_le_one _ (tree.terminalIsometry_gram UA Ub)

end OptimalQLS.LowerBounds
