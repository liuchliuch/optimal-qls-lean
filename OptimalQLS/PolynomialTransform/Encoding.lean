import OptimalQLS.PolynomialTransform.EvenDilation
import OptimalQLS.PolynomialTransform.Spectral

/-! # Computational-signal-register endpoint of bounded even transformation -/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Matrix Polynomial
open scoped Matrix.Norms.L2Operator
variable {W D S : Type*} [Fintype W] [DecidableEq W] [Fintype D] [DecidableEq D]
  [Fintype S] [DecidableEq S]

/-- Compression into the literal first direct-sum sector. -/
theorem leftSumInsertion_compression (E : Matrix W D ℂ)
    (V : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    (leftSumInsertion E)ᴴ*V*leftSumInsertion E=Eᴴ*V.toBlocks₁₁*E := by
  rw [← Matrix.fromBlocks_toBlocks V]
  simp [leftSumInsertion,Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromCols_mul_fromBlocks,Matrix.fromCols_mul_fromRows]

/-- Both additional labels are initialized to their actual zero sectors. -/
theorem evenQSVTInsertion_eq (E : Matrix W D ℂ) :
    evenQSVTInsertion E=leftSumInsertion (leftSumInsertion E) := by
  simp [evenQSVTInsertion,leftSumInsertion,duplicateInsertion,
    Matrix.fromRows_mul,Matrix.fromBlocks_mul_fromRows]

/-- Static basis relabeling puts both extra qubits beside the original signal. -/
def twoLabelSignalEquiv (S D : Type*) :
    (((S × D) ⊕ (S × D)) ⊕ ((S × D) ⊕ (S × D))) ≃ (((Bool × Bool) × S) × D) where
  toFun w := match w with
    | .inl (.inl (s,d)) => (((false,false),s),d)
    | .inl (.inr (s,d)) => (((false,true),s),d)
    | .inr (.inl (s,d)) => (((true,false),s),d)
    | .inr (.inr (s,d)) => (((true,true),s),d)
  invFun w := match w.1.1.1,w.1.1.2 with
    | false,false => .inl (.inl (w.1.2,w.2))
    | false,true => .inl (.inr (w.1.2,w.2))
    | true,false => .inr (.inl (w.1.2,w.2))
    | true,true => .inr (.inr (w.1.2,w.2))
  left_inv w := by rcases w with (⟨s,d⟩|⟨s,d⟩)|(⟨s,d⟩|⟨s,d⟩) <;> rfl
  right_inv w := by rcases w with ⟨⟨⟨b,c⟩,s⟩,d⟩; cases b <;> cases c <;> rfl

set_option maxHeartbeats 800000 in
theorem twoLabel_signalBlock (s₀ : S)
    (V : Matrix.unitaryGroup (((S × D) ⊕ (S × D)) ⊕ ((S × D) ⊕ (S × D))) ℂ) :
    signalBlock ((false,false),s₀) (rewireUnitary (twoLabelSignalEquiv S D) V) =
      (evenQSVTInsertion (signalInjection (D := D) s₀))ᴴ*(V : Matrix _ _ ℂ)*
        evenQSVTInsertion (signalInjection s₀) := by
  rw [evenQSVTInsertion_eq,leftSumInsertion_compression,leftSumInsertion_compression]
  ext i j
  rw [signalBlock_entries]
  exact (signalBlock_entries (S := S) (D := D) s₀
    ((V : Matrix (((S × D) ⊕ (S × D)) ⊕ ((S × D) ⊕ (S × D)))
      (((S × D) ⊕ (S × D)) ⊕ ((S × D) ⊕ (S × D))) ℂ).toBlocks₁₁.toBlocks₁₁) i j).symm

/-- The final concrete unitary in ordinary signal/data register order. -/
def boundedTransformUnitary (s₀ : S) (U : Matrix.unitaryGroup (S × D) ℂ)
    (z₀ : Circle) (zs : List Circle) : Matrix.unitaryGroup (((Bool × Bool) × S) × D) ℂ :=
  rewireUnitary (twoLabelSignalEquiv S D)
    (evenQSVTUnitary (signalInjection s₀) (signalInjection_isometry s₀) U z₀ zs)

/-- Exact block-encoding realization of every bounded even real polynomial.
There are precisely two extra binary signal labels; no realization or phase
existence hypothesis appears in this theorem. -/
theorem bounded_even_exact_encoding [Nonempty D] (s₀ : S) (p : ℝ[X])
    (hp : Function.Even p.eval) (hbound : ∀ x : ℝ, |x| ≤ 1 → |p.eval x| ≤ 1) :
    ∃ (z₀ : Circle) (zs : List Circle), zs.length ≤ p.natDegree ∧
      ∀ (U : Matrix.unitaryGroup (S × D) ℂ) (A : Matrix D D ℂ), A.IsHermitian →
        IsBlockEncoding s₀ 1 0 U A →
        IsBlockEncoding ((false,false),s₀) 1 0 (boundedTransformUnitary s₀ U z₀ zs)
          (Polynomial.aeval A (liftReal p)) := by
  obtain ⟨z₀,zs,hlen,htransform⟩ := bounded_even_matrix_transformation
    (signalInjection (D := D) s₀) (signalInjection_isometry s₀) p hp hbound
  refine ⟨z₀,zs,hlen,?_⟩
  intro U A hA henc
  have hb : (signalInjection (D := D) s₀)ᴴ*(U : Matrix (S × D) (S × D) ℂ)*signalInjection s₀=A := by
    have he := exact_block_eq henc
    simpa only [one_smul,signalBlock] using he.symm
  refine ⟨by norm_num,by norm_num,?_⟩
  rw [one_smul,boundedTransformUnitary,twoLabel_signalBlock,htransform U A hA hb,sub_self,norm_zero]

/-- Matrix polynomial and continuous-operator polynomial conventions agree. -/
theorem polynomial_matrix_to_operator (A : Matrix D D ℂ) (p : ℝ[X]) :
    Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) (Polynomial.aeval A (liftReal p)) =
      polynomialOperator p (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A) := by
  rw [← Polynomial.aeval_algHom_apply]
  unfold polynomialOperator liftReal
  symm
  exact Polynomial.aeval_eq_aeval_map (R := ℝ) (T := ℂ)
    (S := EuclideanSpace ℂ D →L[ℂ] EuclideanSpace ℂ D) (φ := algebraMap ℝ ℂ)
    (IsScalarTower.algebraMap_eq ℝ ℂ _).symm p _

end OptimalQLS.PolynomialTransform
