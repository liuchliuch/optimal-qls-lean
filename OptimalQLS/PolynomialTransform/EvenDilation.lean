import OptimalQLS.PolynomialTransform.RealPartExtraction
import OptimalQLS.LowerBounds.HermitianDilation

/-! # Bounded even polynomial realization for arbitrary block-encoding oracles -/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Polynomial Matrix
variable {W D : Type*} [Fintype W] [DecidableEq W] [Fintype D] [DecidableEq D]

/-- Duplicate a matrix on the two data-label sectors. -/
def duplicateMatrix : Matrix D D ℂ →ₐ[ℂ] Matrix (D ⊕ D) (D ⊕ D) ℂ where
  toFun A := Matrix.fromBlocks A 0 0 A
  map_zero' := by simp
  map_one' := by simp
  map_add' A B := by simp [Matrix.fromBlocks_add]
  map_mul' A B := by simp [Matrix.fromBlocks_multiply]
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one]
    ext i j
    cases i <;> cases j <;> simp [Matrix.one_apply]

/-- Squaring the actual Hermitian dilation duplicates A² for Hermitian A. -/
theorem hermitianDilation_square (A : Matrix D D ℂ) (hA : A.IsHermitian) :
    (LowerBounds.hermitianDilation A)^2=duplicateMatrix (A^2) := by
  rw [pow_two,LowerBounds.hermitianDilation,Matrix.fromBlocks_multiply]
  simp [hA.eq,duplicateMatrix,pow_two]

/-- Actual even polynomial evaluation on the Hermitian dilation is block diagonal. -/
theorem even_polynomial_dilation (A : Matrix D D ℂ) (hA : A.IsHermitian)
    (p : ℝ[X]) (hp : Function.Even p.eval) :
    Polynomial.aeval (LowerBounds.hermitianDilation A) (liftReal p) =
      duplicateMatrix (Polynomial.aeval A (liftReal p)) := by
  have he := Completion.expand_contract_even p (even_polynomial_parity p hp)
  have hcomplex : liftReal p=(liftReal (contract 2 p)).comp (X^2) := by
    conv_lhs => rw [← he]
    simp [liftReal,Polynomial.map_comp,expand_eq_comp_X_pow]
  rw [hcomplex,Polynomial.aeval_comp,Polynomial.aeval_comp]
  simp only [map_pow,aeval_X]
  rw [hermitianDilation_square A hA,Polynomial.aeval_algHom_apply]

/-- The original signal insertion is duplicated alongside the oracle. -/
def duplicateInsertion (E : Matrix W D ℂ) : Matrix (W ⊕ W) (D ⊕ D) ℂ :=
  Matrix.fromBlocks E 0 0 E

@[simp] theorem duplicateInsertion_isometry (E : Matrix W D ℂ) (hE : Eᴴ*E=1) :
    (duplicateInsertion E)ᴴ*duplicateInsertion E=1 := by
  simp [duplicateInsertion,Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_multiply,hE]

/-- Dilation compresses to the actual dilation of the encoded matrix. -/
theorem duplicateInsertion_block (E : Matrix W D ℂ) (U : Matrix.unitaryGroup W ℂ)
    (A : Matrix D D ℂ) (hblock : Eᴴ*(U : Matrix W W ℂ)*E=A) :
    (duplicateInsertion E)ᴴ*(LowerBounds.hermitianUnitaryDilation U : Matrix (W ⊕ W) (W ⊕ W) ℂ)*
      duplicateInsertion E=LowerBounds.hermitianDilation A := by
  have hadj : Eᴴ*(U : Matrix W W ℂ)ᴴ*E=Aᴴ := by
    have h := congrArg Matrix.conjTranspose hblock
    simpa only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc] using h
  simp [duplicateInsertion,LowerBounds.hermitianUnitaryDilation,LowerBounds.hermitianDilation,
    Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_multiply,hblock,hadj]

/-- Two additional zero labels: one for the dilation, one for real-part extraction. -/
def evenQSVTInsertion (E : Matrix W D ℂ) : Matrix ((W ⊕ W) ⊕ (W ⊕ W)) D ℂ :=
  leftSumInsertion (duplicateInsertion E)*leftSumInsertion (1 : Matrix D D ℂ)

@[simp] theorem evenQSVTInsertion_isometry (E : Matrix W D ℂ) (hE : Eᴴ*E=1) :
    (evenQSVTInsertion E)ᴴ*evenQSVTInsertion E=1 := by
  unfold evenQSVTInsertion
  rw [Matrix.conjTranspose_mul]
  calc
    _ = (leftSumInsertion (1 : Matrix D D ℂ))ᴴ*
      ((leftSumInsertion (duplicateInsertion E))ᴴ*leftSumInsertion (duplicateInsertion E))*
        leftSumInsertion (1 : Matrix D D ℂ) := by simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [leftSumInsertion_isometry _ (duplicateInsertion_isometry E hE),Matrix.mul_one,
        leftSumInsertion_isometry _ (by simp)]

/-- Fully explicit unitary built from phases, the original oracle's Hermitian
dilation, and one-qubit coherent averaging. -/
def evenQSVTUnitary (E : Matrix W D ℂ) (hE : Eᴴ*E=1)
    (U : Matrix.unitaryGroup W ℂ) (z₀ : Circle) (zs : List Circle) :
    Matrix.unitaryGroup ((W ⊕ W) ⊕ (W ⊕ W)) ℂ :=
  coherentAverage
    (hermitianPhaseWord (duplicateInsertion E) (duplicateInsertion_isometry E hE)
      (LowerBounds.hermitianUnitaryDilation U) z₀ zs)
    (hermitianPhaseWord (duplicateInsertion E) (duplicateInsertion_isometry E hE)
      (LowerBounds.hermitianUnitaryDilation U) z₀⁻¹ (zs.map Inv.inv))

/-- Exact selected-block realization for an arbitrary, possibly non-Hermitian
block-encoding oracle, using only the Hermiticity of its encoded block. -/
theorem evenQSVTUnitary_compression (E : Matrix W D ℂ) (hE : Eᴴ*E=1)
    (U : Matrix.unitaryGroup W ℂ) (A : Matrix D D ℂ) (hA : A.IsHermitian)
    (hblock : Eᴴ*(U : Matrix W W ℂ)*E=A)
    (p B C₀ : ℝ[X]) (hp : Function.Even p.eval) (z₀ : Circle) (zs : List Circle)
    (hseq : QSP.sequencePair z₀ zs=(completedP p B,completedQ C₀)) :
    (evenQSVTInsertion E)ᴴ*(evenQSVTUnitary E hE U z₀ zs :
      Matrix ((W ⊕ W) ⊕ (W ⊕ W)) ((W ⊕ W) ⊕ (W ⊕ W)) ℂ)*evenQSVTInsertion E =
      Polynomial.aeval A (liftReal p) := by
  let J := leftSumInsertion (duplicateInsertion E)
  let L := leftSumInsertion (1 : Matrix D D ℂ)
  have hdU : (LowerBounds.hermitianUnitaryDilation U : Matrix (W ⊕ W) (W ⊕ W) ℂ)ᴴ=
      LowerBounds.hermitianUnitaryDilation U := (LowerBounds.hermitianDilation_hermitian (U : Matrix W W ℂ)).eq
  have hc := coherent_realPart_compression (duplicateInsertion E) (duplicateInsertion_isometry E hE)
    (LowerBounds.hermitianUnitaryDilation U) hdU (LowerBounds.hermitianDilation A)
    (LowerBounds.hermitianDilation_hermitian A) (duplicateInsertion_block E U A hblock)
    p B C₀ z₀ zs hseq
  change (J*L)ᴴ*(evenQSVTUnitary E hE U z₀ zs : Matrix _ _ ℂ)*(J*L)=_
  rw [Matrix.conjTranspose_mul]
  calc
    _ = Lᴴ*(Jᴴ*(evenQSVTUnitary E hE U z₀ zs : Matrix _ _ ℂ)*J)*L := by simp only [Matrix.mul_assoc]
    _ = Lᴴ*Polynomial.aeval (LowerBounds.hermitianDilation A) (liftReal p)*L := by
      dsimp only [J,evenQSVTUnitary]
      rw [hc]
    _ = Lᴴ*duplicateMatrix (Polynomial.aeval A (liftReal p))*L := by rw [even_polynomial_dilation A hA p hp]
    _ = Polynomial.aeval A (liftReal p) := by
      simp [L,leftSumInsertion,duplicateMatrix,Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
        Matrix.fromCols_mul_fromBlocks,Matrix.fromCols_mul_fromRows]

/-- The matrix realization portion of Lemma 2.4, with phases uniform in the
input oracle and two explicit additional binary workspace labels. -/
theorem bounded_even_matrix_transformation (E : Matrix W D ℂ) (hE : Eᴴ*E=1)
    (p : ℝ[X]) (hp : Function.Even p.eval)
    (hbound : ∀ x : ℝ, |x| ≤ 1 → |p.eval x| ≤ 1) :
    ∃ (z₀ : Circle) (zs : List Circle), zs.length ≤ p.natDegree ∧
      ∀ (U : Matrix.unitaryGroup W ℂ) (A : Matrix D D ℂ), A.IsHermitian →
        Eᴴ*(U : Matrix W W ℂ)*E=A →
        (evenQSVTInsertion E)ᴴ*(evenQSVTUnitary E hE U z₀ zs :
          Matrix ((W ⊕ W) ⊕ (W ⊕ W)) ((W ⊕ W) ⊕ (W ⊕ W)) ℂ)*evenQSVTInsertion E =
          Polynomial.aeval A (liftReal p) := by
  obtain ⟨B,C₀,z₀,zs,hseq,hlen⟩ := bounded_even_phase_synthesis p hp hbound
  exact ⟨z₀,zs,hlen,fun U A hA hb => evenQSVTUnitary_compression E hE U A hA hb p B C₀ hp z₀ zs hseq⟩

end OptimalQLS.PolynomialTransform
