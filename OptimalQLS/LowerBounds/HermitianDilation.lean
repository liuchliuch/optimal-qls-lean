import OptimalQLS.LowerBounds.BlockNorms
import OptimalQLS.InputReflection
import OptimalQLS.BlockEncoding

/-!
# Concrete Hermitian dilation identities and block encodings

All operators are literal two-by-two block matrices. Exact norm preservation,
actual inverse formulas, embedded solution vectors, and signal compression
are proved here for reuse in Proposition2.3 and the lower-bound family.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix
variable {D : Type*} [Fintype D] [DecidableEq D]

def hermitianDilation (G : Matrix D D ℂ) : Matrix (D ⊕ D) (D ⊕ D) ℂ :=
  Matrix.fromBlocks 0 G G.conjTranspose 0

theorem hermitianDilation_hermitian (G : Matrix D D ℂ) : (hermitianDilation G).IsHermitian := by
  simp [hermitianDilation, Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose]

theorem hermitianDilation_factor (G : Matrix D D ℂ) :
    hermitianDilation G = Matrix.fromBlocks G 0 0 G.conjTranspose *
      (OptimalQLS.swapPublicPrivate : Matrix.unitaryGroup (D ⊕ D) ℂ) := by
  change _ = Matrix.fromBlocks G 0 0 G.conjTranspose * Matrix.fromBlocks 0 1 1 0
  rw [Matrix.fromBlocks_multiply]
  simp [hermitianDilation]

/-- Hermitian dilation exactly preserves the Euclidean operator norm. -/
theorem hermitianDilation_norm (G : Matrix D D ℂ) : ‖hermitianDilation G‖ = ‖G‖ := by
  rw [hermitianDilation_factor, CStarRing.norm_mul_coe_unitary, blockDiagonal_norm,
    Matrix.l2_opNorm_conjTranspose, max_self]

def hermitianInverseCandidate (T : Matrix D D ℂ) : Matrix (D ⊕ D) (D ⊕ D) ℂ :=
  Matrix.fromBlocks 0 T.conjTranspose T 0

theorem hermitianInverseCandidate_mul (G T : Matrix D D ℂ) (hTG : T * G = 1) (hGT : G * T = 1) :
    hermitianInverseCandidate T * hermitianDilation G = 1 := by
  have hstar : T.conjTranspose * G.conjTranspose = 1 := by
    simpa using congrArg Matrix.conjTranspose hGT
  rw [hermitianInverseCandidate, hermitianDilation, Matrix.fromBlocks_multiply]
  simp [hTG, hstar]

/-- Formula uses the actual nonsingular matrix inverse, not a formal inverse symbol. -/
theorem hermitianDilation_inverse (G T : Matrix D D ℂ) (hTG : T * G = 1) (hGT : G * T = 1) :
    (hermitianDilation G)⁻¹ = hermitianInverseCandidate T :=
  Matrix.inv_eq_left_inv (hermitianInverseCandidate_mul G T hTG hGT)

theorem hermitianInverseCandidate_norm (T : Matrix D D ℂ) : ‖hermitianInverseCandidate T‖ = ‖T‖ := by
  have heq : hermitianInverseCandidate T = hermitianDilation T.conjTranspose := by
    simp [hermitianInverseCandidate, hermitianDilation]
  rw [heq, hermitianDilation_norm, Matrix.l2_opNorm_conjTranspose]

theorem hermitianDilation_inverse_norm (G T : Matrix D D ℂ) (hTG : T * G = 1) (hGT : G * T = 1) :
    ‖(hermitianDilation G)⁻¹‖ = ‖T‖ := by
  rw [hermitianDilation_inverse G T hTG hGT, hermitianInverseCandidate_norm]

/-- A source on the first half gives the inverse solution on the second half. -/
theorem hermitianDilation_inverse_source (G T : Matrix D D ℂ) (hTG : T * G = 1) (hGT : G * T = 1)
    (b : D → ℂ) :
    (hermitianDilation G)⁻¹ *ᵥ Sum.elim b (0 : D → ℂ) = Sum.elim (0 : D → ℂ) (T *ᵥ b) := by
  rw [hermitianDilation_inverse G T hTG hGT, hermitianInverseCandidate, Matrix.fromBlocks_mulVec]
  simp [Function.comp_def]
  change Sum.elim (T.conjTranspose *ᵥ (0 : D → ℂ)) (T *ᵥ b) = _
  rw [Matrix.mulVec_zero]

theorem hermitianDilation_solution_norm (G T : Matrix D D ℂ) (hTG : T * G = 1) (hGT : G * T = 1)
    (b : D → ℂ) :
    ‖WithLp.toLp 2 ((hermitianDilation G)⁻¹ *ᵥ Sum.elim b (0 : D → ℂ))‖ =
      ‖WithLp.toLp 2 (T *ᵥ b)‖ := by
  rw [hermitianDilation_inverse_source G T hTG hGT, sumElim_norm_right]

/-- Equal real eigenvectors on both halves yield a dilation eigenvector. -/
theorem hermitianDilation_eigen (G : Matrix D D ℂ) (v : D → ℂ) (a : ℂ)
    (hG : G *ᵥ v = a • v) (hGt : G.conjTranspose *ᵥ v = a • v) :
    hermitianDilation G *ᵥ Sum.elim v v = a • Sum.elim v v := by
  rw [hermitianDilation, Matrix.fromBlocks_mulVec]
  simp [Function.comp_def, hG, hGt]
  funext i
  cases i <;> rfl

/-- Dilation of a unitary is a literal Hermitian unitary. -/
def hermitianUnitaryDilation (U : Matrix.unitaryGroup D ℂ) : Matrix.unitaryGroup (D ⊕ D) ℂ :=
  ⟨hermitianDilation (U : Matrix D D ℂ), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      (hermitianDilation_hermitian (U : Matrix D D ℂ))]
    rw [hermitianDilation, Matrix.fromBlocks_multiply]
    have hU : (U : Matrix D D ℂ) * (U : Matrix D D ℂ).conjTranspose = 1 := U.property.2
    have hUt : (U : Matrix D D ℂ).conjTranspose * (U : Matrix D D ℂ) = 1 := U.property.1
    simp [hU, hUt]⟩

def distributeSignal (S D : Type*) : ((S × D) ⊕ (S × D)) ≃ S × (D ⊕ D) where
  toFun x := match x with | .inl (s, d) => (s, .inl d) | .inr (s, d) => (s, .inr d)
  invFun x := match x.2 with | .inl d => .inl (x.1, d) | .inr d => .inr (x.1, d)
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨s, d⟩; cases d <;> rfl

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The same signal register block-encodes the Hermitian dilation. -/
def dilationEncoding (U : Matrix.unitaryGroup (S × D) ℂ) :
    Matrix.unitaryGroup (S × (D ⊕ D)) ℂ :=
  OptimalQLS.rewireUnitary (distributeSignal S D) (hermitianUnitaryDilation U)

theorem dilationEncoding_signalBlock (s : S) (U : Matrix.unitaryGroup (S × D) ℂ) :
    OptimalQLS.signalBlock s (dilationEncoding U : Matrix (S × (D ⊕ D)) (S × (D ⊕ D)) ℂ) =
      hermitianDilation (OptimalQLS.signalBlock s (U : Matrix (S × D) (S × D) ℂ)) := by
  ext i j
  cases i <;> cases j <;>
    simp [OptimalQLS.signalBlock_entries, dilationEncoding, OptimalQLS.rewireUnitary,
      distributeSignal, hermitianUnitaryDilation, hermitianDilation, Matrix.conjTranspose_apply]

theorem hermitianDilation_real_smul (a : ℝ) (G : Matrix D D ℂ) :
    hermitianDilation (a • G) = a • hermitianDilation G := by
  simp [hermitianDilation, Matrix.fromBlocks_smul]

/-- Exact block encodings pass through dilation with unchanged signal size. -/
theorem dilationEncoding_exact [Nonempty D] (s : S) (alpha : ℝ)
    (U : Matrix.unitaryGroup (S × D) ℂ) (G : Matrix D D ℂ)
    (h : OptimalQLS.IsBlockEncoding s alpha 0 U G) :
    OptimalQLS.IsBlockEncoding s alpha 0 (dilationEncoding U) (hermitianDilation G) := by
  refine ⟨h.1, by norm_num, ?_⟩
  rw [dilationEncoding_signalBlock, OptimalQLS.exact_block_eq h, hermitianDilation_real_smul]
  simp

end OptimalQLS.LowerBounds
