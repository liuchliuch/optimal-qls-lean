import OptimalQLS.Reduction.Normalized
import OptimalQLS.Reduction.Extraction
import OptimalQLS.Reduction.Resources
import OptimalQLS.Reduction.Circuits
import OptimalQLS.Reduction.CircuitBridges
import OptimalQLS.Reduction.Promises
import OptimalQLS.Reduction.Physical
import OptimalQLS.PhysicalPadding.Dilation

/-! Proposition 2.3: actual input normalization, extraction, and three-run
amplification. The normalized solver guarantee is the explicit conditional
input to the second statement, as in the paper. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.Reduction
open Matrix LowerBounds Refinement.Repetition
set_option maxHeartbeats 500000
variable {D S : Type*} [Fintype D] [DecidableEq D] [Nonempty D]
  [Fintype S] [DecidableEq S]

theorem proposition23_input (s : S) (zero : D) {α κ estimate ε : ℝ}
    (A : Matrix D D ℂ) (b : D → ℂ)
    (UA : Matrix.unitaryGroup (S × D) ℂ) (Ub : Matrix.unitaryGroup D ℂ)
    (henc : IsBlockEncoding s α 0 UA A) (hA : IsUnit A)
    (hb : ‖WithLp.toLp 2 b‖ = 1) (hprep : ∀ i, Ub i zero = b i)
    (hκ : 2 ≤ κ) (hinv : α * ‖A⁻¹‖ ≤ κ)
    (hε0 : 0 < ε) (hε1 : ε < 1/2)
    (hlo : 3 * (α * ‖WithLp.toLp 2 (A⁻¹ *ᵥ b)‖)/8 ≤ estimate)
    (hhi : estimate ≤ 5 * (α * ‖WithLp.toLp 2 (A⁻¹ *ᵥ b)‖)/2) :
    (normalizedMatrix α A).IsHermitian ∧ IsUnit (normalizedMatrix α A) ∧
    IsBlockEncoding s 1 0 (dilationEncoding UA) (normalizedMatrix α A) ∧
    ‖WithLp.toLp 2 (source b)‖ = 1 ∧
    (∀ i, preparation Ub i (.inl zero) = source b i) ∧
    ‖normalizedMatrix α A‖ ≤ 1 ∧ ‖(normalizedMatrix α A)⁻¹‖ ≤ κ ∧
    2 ≤ κ ∧ 0 < ε/2 ∧ ε/2 < 1/2 ∧
    ‖WithLp.toLp 2 ((normalizedMatrix α A)⁻¹ *ᵥ source b)‖ =
      α * ‖WithLp.toLp 2 (A⁻¹ *ᵥ b)‖ ∧
    3 * ‖WithLp.toLp 2 ((normalizedMatrix α A)⁻¹ *ᵥ source b)‖/8 ≤ estimate ∧
    estimate ≤ 5 * ‖WithLp.toLp 2 ((normalizedMatrix α A)⁻¹ *ᵥ source b)‖/2 := by
  have hn := normalized_bounds s A UA henc hA hinv
  have he := relaxed_estimate_transport henc.1 A hA b hlo hhi
  exact ⟨normalizedMatrix_hermitian α A, normalizedMatrix_isUnit henc.1 A hA,
    normalized_encoding s A UA henc, by rwa [source_norm], preparation_prepares Ub zero b hprep,
    hn.1, hn.2, hκ, by positivity, by linarith,
    normalized_solution_scale henc.1 A hA b, he.1, he.2⟩

/-- The original data register is the right outcome of the literal additional
data qubit. E is a computational-basis relabeling, not an assumption on y. -/
def extractRightEmbedding {d m : ℕ} (E : (Fin d ⊕ Fin d) ≃ Fin m) : Fin d ↪ Fin m where
  toFun i := E (.inr i)
  inj' := E.injective.comp Sum.inr_injective

universe u v
variable {OA : Type u} {OB : Type v} [Fintype OA] [DecidableEq OA]
  [Fintype OB] [DecidableEq OB] {d m w : ℕ}

/-- The same explicit program both achieves the probability guarantee and
returns the correctly normalized extracted state. Reset measurements prove
the retry law; independent attempts are not assumed. -/
theorem proposition23_success (tree : FiniteOracleProgram OA OB m w)
    (E : (Fin d ⊕ Fin d) ≃ Fin m) (zero : Fin w) (out : Fin d)
    (UA : Matrix.unitaryGroup OA ℂ) (Ub : Matrix.unitaryGroup OB ℂ)
    (y : EuclideanSpace ℂ (Fin d ⊕ Fin d)) (x : EuclideanSpace ℂ (Fin d))
    {ε : ℝ} (hy : ‖y‖ = 1) (hx : ‖x‖ = 1)
    (hε0 : 0 < ε) (hε1 : ε < 1/2)
    (herr : ‖y - WithLp.toLp 2 (rightState (fun i => x i))‖ ≤ ε/2)
    (hprob : 2/3 ≤ tree.successProbability UA Ub (basis zero))
    (houtput : tree.conditionalOutput UA Ub (basis zero) =
      pureDensity (fun i => y (E.symm i))) :
    let result := retrySolver tree (extractRightEmbedding E) zero out 3
    (2:ℝ)/3 < result.successProbability UA Ub (basis zero) ∧
    result.conditionalOutput UA Ub (basis zero) =
      pureDensity (fun i => (NormedSpace.normalize (rightPart y)) i) ∧
    ‖NormedSpace.normalize (rightPart y) - x‖ ≤ ε ∧
    ‖NormedSpace.normalize (rightPart y)‖ = 1 ∧
    1 - ε^2/4 ≤ ‖rightPart y‖^2 ∧
    matrixDepth result ≤ 3 * matrixDepth tree ∧
    result.vectorDepth ≤ 3 * tree.vectorDepth ∧
    instrumentDepth result ≤ 3 * (instrumentDepth tree + 2) + 1 := by
  dsimp only
  have hg := extraction_guarantee y x hy hx hε0 hε1 herr
  have hp0 : 0 < tree.successProbability UA Ub (basis zero) := by linarith
  have hm := attemptMass_of_pure_output tree (extractRightEmbedding E) zero UA Ub
    (fun i => y (E.symm i)) hp0 houtput
  have hmass : attemptMass tree (extractRightEmbedding E) zero UA Ub =
      tree.successProbability UA Ub (basis zero) * ‖rightPart y‖^2 := by
    simpa [extractRightEmbedding, bornMass_eq_norm_sq, rightPart] using hm
  have hmasslow : 3/8 ≤ attemptMass tree (extractRightEmbedding E) zero UA Ub := by
    rw [hmass]
    have hmul := mul_le_mul hprob hg.2.2.2.1 (by norm_num : (0:ℝ) ≤ 9/16) hp0.le
    norm_num at hmul
    exact hmul
  have he : 0 < bornMass (fun i => y (E.symm (extractRightEmbedding E i))) := by
    simp only [extractRightEmbedding, Function.Embedding.coeFn_mk, Equiv.symm_apply_apply]
    rw [bornMass_eq_norm_sq]
    change 0 < ‖rightPart y‖^2
    linarith [hg.2.2.2.1]
  have hout := retrySolver_pure_output tree (extractRightEmbedding E) zero out 3 UA Ub
    (fun i => y (E.symm i)) hp0 houtput he (by decide)
  refine ⟨three_attempts_success tree _ zero out UA Ub hmasslow, ?_,
    hg.2.2.2.2.1, hg.2.2.2.2.2, hg.2.2.1,
    retrySolver_matrixDepth tree _ zero out 3, retrySolver_vectorDepth tree _ zero out 3,
    retrySolver_instrumentDepth tree _ zero out 3⟩
  simpa [extractRightEmbedding, rightPart] using hout

/-- The extraction theorem targeting the original, actual inverse solution,
with the normalized dilation target derived from A and alpha. -/
theorem proposition23_solution (tree : FiniteOracleProgram OA OB m w)
    (E : (Fin d ⊕ Fin d) ≃ Fin m) (zero : Fin w) (out : Fin d)
    (UA : Matrix.unitaryGroup OA ℂ) (Ub : Matrix.unitaryGroup OB ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) (b : Fin d → ℂ) {α ε : ℝ}
    (hα : 0 < α) (hA : IsUnit A) (hb : ‖WithLp.toLp 2 b‖ = 1)
    (y : EuclideanSpace ℂ (Fin d ⊕ Fin d)) (hy : ‖y‖ = 1)
    (hε0 : 0 < ε) (hε1 : ε < 1/2)
    (herr : ‖y - NormedSpace.normalize
      (WithLp.toLp 2 ((normalizedMatrix α A)⁻¹ *ᵥ source b))‖ ≤ ε/2)
    (hprob : 2/3 ≤ tree.successProbability UA Ub (basis zero))
    (houtput : tree.conditionalOutput UA Ub (basis zero) =
      pureDensity (fun i => y (E.symm i))) :
    let result := retrySolver tree (extractRightEmbedding E) zero out 3
    ∃ z : EuclideanSpace ℂ (Fin d), ‖z‖ = 1 ∧
      ‖z - NormedSpace.normalize (WithLp.toLp 2 (A⁻¹ *ᵥ b))‖ ≤ ε ∧
      (2:ℝ)/3 < result.successProbability UA Ub (basis zero) ∧
      result.conditionalOutput UA Ub (basis zero) = pureDensity (fun i => z i) ∧
      matrixDepth result ≤ 3 * matrixDepth tree ∧
      result.vectorDepth ≤ 3 * tree.vectorDepth ∧
      instrumentDepth result ≤ 3 * (instrumentDepth tree + 2) + 1 := by
  rw [normalized_solution_direction hα A hA b] at herr
  have h := proposition23_success tree E zero out UA Ub y
    (NormedSpace.normalize (WithLp.toLp 2 (A⁻¹ *ᵥ b))) hy
    (normalized_original_solution_unit A hA b hb) hε0 hε1 herr hprob houtput
  exact ⟨NormedSpace.normalize (rightPart y), h.2.2.2.1, h.2.2.1,
    h.1, h.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

end OptimalQLS.Reduction
