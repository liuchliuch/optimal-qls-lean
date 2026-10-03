import OptimalQLS.PolynomialTransform.HermitianQSP
import OptimalQLS.FractionalTransducer
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! # Exact coherent real-part extraction with one ancillary qubit -/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Polynomial Matrix
open scoped ComplexConjugate
variable {W D : Type*} [Fintype W] [DecidableEq W] [Fintype D] [DecidableEq D]

/-- The actual two-branch unitary selector. -/
def sumUnitary (U V : Matrix.unitaryGroup W ℂ) : Matrix.unitaryGroup (W ⊕ W) ℂ :=
  ⟨Matrix.fromBlocks (U : Matrix W W ℂ) 0 0 V, by
    rw [Matrix.mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose,
      Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_multiply]
    have hu : (U : Matrix W W ℂ)*(U : Matrix W W ℂ)ᴴ=1 := U.property.2
    have hv : (V : Matrix W W ℂ)*(V : Matrix W W ℂ)ᴴ=1 := V.property.2
    simp [hu,hv]⟩

def halfAmplitude : ℝ := Real.sqrt (1/2)

@[simp] theorem halfAmplitude_sq : halfAmplitude^2=1/2 := by
  exact Real.sq_sqrt (by norm_num)

theorem halfAmplitude_bound : |(-halfAmplitude : ℝ)| < 1 := by
  have hp : 0 ≤ halfAmplitude := Real.sqrt_nonneg (1/2 : ℝ)
  have hs := halfAmplitude_sq
  rw [abs_neg,abs_of_nonneg hp]
  nlinarith

/-- A literal Hadamard mixing of two copies of the workspace. -/
def sumHadamard (W : Type*) [Fintype W] [DecidableEq W] : Matrix.unitaryGroup (W ⊕ W) ℂ :=
  ⟨fractionalMix (-halfAmplitude),fractionalMix_unitary halfAmplitude_bound⟩

theorem sumHadamard_matrix : (sumHadamard W : Matrix (W ⊕ W) (W ⊕ W) ℂ) =
    Matrix.fromBlocks (halfAmplitude • (1 : Matrix W W ℂ)) (halfAmplitude • 1)
      (halfAmplitude • 1) ((-halfAmplitude) • 1) := by
  change fractionalMix (-halfAmplitude)=_
  unfold fractionalMix
  rw [neg_sq,halfAmplitude_sq]
  norm_num [halfAmplitude]

/-- The coherent average H diag(U,V) H is an explicit unitary. -/
def coherentAverage (U V : Matrix.unitaryGroup W ℂ) : Matrix.unitaryGroup (W ⊕ W) ℂ :=
  sumHadamard W*sumUnitary U V*sumHadamard W

/-- Initialize the averaging qubit in its literal zero sector. -/
def leftSumInsertion (E : Matrix W D ℂ) : Matrix (W ⊕ W) D ℂ := Matrix.fromRows E 0

@[simp] theorem leftSumInsertion_isometry (E : Matrix W D ℂ) (hE : Eᴴ*E=1) :
    (leftSumInsertion E)ᴴ*leftSumInsertion E=1 := by
  simp [leftSumInsertion,Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromCols_mul_fromRows,hE]

/-- Selected-block compression is exactly the arithmetic mean of the two
selected blocks, with no assumed LCU realization. -/
theorem coherentAverage_compression (E : Matrix W D ℂ) (U V : Matrix.unitaryGroup W ℂ) :
    (leftSumInsertion E)ᴴ*(coherentAverage U V : Matrix (W ⊕ W) (W ⊕ W) ℂ)*leftSumInsertion E =
      (1/2 : ℝ) • (Eᴴ*(U : Matrix W W ℂ)*E+Eᴴ*(V : Matrix W W ℂ)*E) := by
  change (Matrix.fromRows E 0)ᴴ*
    ((sumHadamard W : Matrix (W ⊕ W) (W ⊕ W) ℂ)*
      Matrix.fromBlocks (U : Matrix W W ℂ) 0 0 V*(sumHadamard W : Matrix (W ⊕ W) (W ⊕ W) ℂ))*
        Matrix.fromRows E 0 = _
  rw [sumHadamard_matrix,Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply,
    Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose]
  simp only [Matrix.mul_zero,Matrix.zero_mul,Matrix.mul_one,Matrix.one_mul,zero_add,add_zero,
    Matrix.fromCols_mul_fromBlocks,Matrix.fromCols_mul_fromRows,Matrix.conjTranspose_zero,
    Matrix.mul_add,Matrix.add_mul,Matrix.smul_mul,Matrix.mul_smul,smul_zero,smul_smul,
    ← smul_add,← pow_two,halfAmplitude_sq]

namespace QSP
@[simp] theorem conjugate_forwardP (z : Circle) (P Q : ℂ[X]) :
    conjugate (forwardP z P Q) = forwardP z⁻¹ (conjugate P) (conjugate Q) := by
  simp [forwardP]
@[simp] theorem conjugate_forwardQ (z : Circle) (P Q : ℂ[X]) :
    conjugate (forwardQ z P Q) = forwardQ z⁻¹ (conjugate P) (conjugate Q) := by
  simp [forwardQ]

theorem sequencePair_inverse_phases (z₀ : Circle) (zs : List Circle) :
    sequencePair z₀⁻¹ (zs.map Inv.inv) =
      (conjugate (sequencePair z₀ zs).1,conjugate (sequencePair z₀ zs).2) := by
  induction zs with
  | nil => simp [sequencePair]
  | cons z zs ih => simp [sequencePair,ih]
end QSP

/-- The real-part polynomial identity holds in every complex algebra. -/
theorem completedP_average (p B : ℝ[X]) :
    (1/2 : ℝ) • (completedP p B+QSP.conjugate (completedP p B)) = liftReal p := by
  have hs : completedP p B+QSP.conjugate (completedP p B) = liftReal p+liftReal p := by
    simp only [completedP,QSP.conjugate_add,QSP.conjugate_mul,conjugate_liftReal,
      QSP.conjugate_C,RCLike.star_def,Complex.conj_I,map_neg]
    ring
  rw [hs,smul_add,← add_smul]
  norm_num

/-- Matrix-only real-part extraction gives the exact requested p(A). -/
theorem coherent_realPart_compression (E : Matrix W D ℂ) (hE : Eᴴ*E=1)
    (U : Matrix.unitaryGroup W ℂ) (hU : (U : Matrix W W ℂ)ᴴ=U)
    (A : Matrix D D ℂ) (hA : A.IsHermitian) (hblock : Eᴴ*(U : Matrix W W ℂ)*E=A)
    (p B C₀ : ℝ[X]) (z₀ : Circle) (zs : List Circle)
    (hseq : QSP.sequencePair z₀ zs=(completedP p B,completedQ C₀)) :
    (leftSumInsertion E)ᴴ*(coherentAverage
      (hermitianPhaseWord E hE U z₀ zs)
      (hermitianPhaseWord E hE U z₀⁻¹ (zs.map Inv.inv)) : Matrix (W ⊕ W) (W ⊕ W) ℂ)*
        leftSumInsertion E = Polynomial.aeval A (liftReal p) := by
  rw [coherentAverage_compression,hermitianPhaseWord_compression E hE U hU A hA hblock,
    hermitianPhaseWord_compression E hE U hU A hA hblock,QSP.sequencePair_inverse_phases,hseq]
  change (1/2 : ℝ) • ((Polynomial.aeval A) (completedP p B)+
    (Polynomial.aeval A) (QSP.conjugate (completedP p B)))=_
  rw [← map_add]
  have hm := congrArg (Polynomial.aeval A) (completedP_average p B)
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul] at hm ⊢
  exact hm

end OptimalQLS.PolynomialTransform
