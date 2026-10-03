import OptimalQLS.PolynomialTransform.ProjectedPhases
import OptimalQLS.PolynomialTransform.BoundedQSP
import Mathlib.Analysis.Matrix.Spectrum

/-! # Matrix-level signal-space realization of QSP for a Hermitian unitary oracle -/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Polynomial Matrix
open scoped ComplexConjugate
variable {W D : Type*} [Fintype W] [DecidableEq W] [Fintype D] [DecidableEq D]

/-- The actual part of U E orthogonal to the encoded signal block. -/
def signalLeakage (E : Matrix W D ℂ) (U : Matrix W W ℂ) (A : Matrix D D ℂ) : Matrix W D ℂ :=
  U*E-E*A

theorem signalLeakage_orthogonal (E : Matrix W D ℂ) (hE : Eᴴ*E=1)
    (U : Matrix W W ℂ) (A : Matrix D D ℂ) (hblock : Eᴴ*U*E=A) :
    Eᴴ*signalLeakage E U A=0 := by
  unfold signalLeakage
  rw [Matrix.mul_sub,← Matrix.mul_assoc,hblock,← Matrix.mul_assoc,hE,Matrix.one_mul,sub_self]

theorem hermitian_oracle_sq (U : Matrix.unitaryGroup W ℂ) (hU : (U : Matrix W W ℂ)ᴴ=U) :
    (U : Matrix W W ℂ)*(U : Matrix W W ℂ)=1 := by
  calc
    (U : Matrix W W ℂ)*(U : Matrix W W ℂ) = (U : Matrix W W ℂ)ᴴ*(U : Matrix W W ℂ) := by rw [hU]
    _ = 1 := U.property.1

theorem oracle_mul_signalLeakage (E : Matrix W D ℂ)
    (U : Matrix.unitaryGroup W ℂ) (hU : (U : Matrix W W ℂ)ᴴ=U) (A : Matrix D D ℂ) :
    (U : Matrix W W ℂ)*signalLeakage E U A =
      E*(1-A*A)-signalLeakage E U A*A := by
  have hu := hermitian_oracle_sq U hU
  unfold signalLeakage
  simp only [Matrix.mul_sub,Matrix.sub_mul,← Matrix.mul_assoc,hu,Matrix.one_mul,Matrix.mul_one]
  abel

/-- The two invariant-column equations, including the endpoint eigenvalues
where the leakage columns may vanish. No normalization by sqrt(1-λ²) is used. -/
theorem hermitianSignal_columns (E : Matrix W D ℂ) (hE : Eᴴ*E=1)
    (U : Matrix.unitaryGroup W ℂ) (hU : (U : Matrix W W ℂ)ᴴ=U)
    (A : Matrix D D ℂ) (hblock : Eᴴ*(U : Matrix W W ℂ)*E=A) :
    let F := signalLeakage E U A
    (hermitianSignal E hE U : Matrix W W ℂ)*E = E*A+Complex.I • F ∧
    (hermitianSignal E hE U : Matrix W W ℂ)*F = Complex.I • (E*(1-A*A))+F*A := by
  dsimp only
  let D₀ := signalBasisPhase E hE
  have hDE : (D₀ : Matrix W W ℂ)*E=E := by
    simpa only [D₀,signalBasisPhase,Circle.coe_one,one_smul] using
      insertionPhases_mul_E E hE 1 circleI
  have hDF : (D₀ : Matrix W W ℂ)*signalLeakage E U A = Complex.I • signalLeakage E U A :=
    insertionPhases_mul_orthogonal E _ hE (signalLeakage_orthogonal E hE U A hblock) 1 circleI
  have hUE : (U : Matrix W W ℂ)*E = E*A+signalLeakage E U A := by
    unfold signalLeakage
    abel
  constructor
  · change ((D₀ : Matrix W W ℂ)*(U : Matrix W W ℂ)*(D₀ : Matrix W W ℂ))*E = _
    rw [Matrix.mul_assoc,Matrix.mul_assoc,hDE,hUE,Matrix.mul_add,← Matrix.mul_assoc,hDE,hDF]
  · change ((D₀ : Matrix W W ℂ)*(U : Matrix W W ℂ)*(D₀ : Matrix W W ℂ))*signalLeakage E U A = _
    rw [Matrix.mul_assoc,Matrix.mul_assoc,hDF,Matrix.mul_smul,oracle_mul_signalLeakage E U hU A,
      Matrix.mul_smul,Matrix.mul_sub,← Matrix.mul_assoc,hDE,← Matrix.mul_assoc,hDF,
      Matrix.smul_mul,smul_sub,smul_smul]
    simp [Complex.I_mul_I]

/-- Finite unitary word with actual signal and phase operators. -/
def unitaryPhaseWord (S : Matrix.unitaryGroup W ℂ) (Φ : Circle → Matrix.unitaryGroup W ℂ)
    (z₀ : Circle) : List Circle → Matrix.unitaryGroup W ℂ
  | [] => Φ z₀
  | z::zs => unitaryPhaseWord S Φ z₀ zs*S*Φ z

/-- Exact recurrence on a possibly degenerate two-vector invariant pair. -/
theorem unitaryPhaseWord_pair_action
    (S : Matrix.unitaryGroup W ℂ) (Φ : Circle → Matrix.unitaryGroup W ℂ)
    (y f : W → ℂ) (x : ℝ)
    (hSy : (S : Matrix W W ℂ)*ᵥy=(x : ℂ) • y+Complex.I • f)
    (hSf : (S : Matrix W W ℂ)*ᵥf=(Complex.I*(1-(x : ℂ)^2)) • y+(x : ℂ) • f)
    (hΦy : ∀ z, (Φ z : Matrix W W ℂ)*ᵥy=(z : ℂ) • y)
    (hΦf : ∀ z, (Φ z : Matrix W W ℂ)*ᵥf=((z⁻¹ : Circle) : ℂ) • f)
    (z₀ : Circle) (zs : List Circle) :
    let P := (QSP.sequencePair z₀ zs).1
    let Q := (QSP.sequencePair z₀ zs).2
    (unitaryPhaseWord S Φ z₀ zs : Matrix W W ℂ)*ᵥy =
      P.eval (x : ℂ) • y+(Complex.I*star (Q.eval (x : ℂ))) • f ∧
    (unitaryPhaseWord S Φ z₀ zs : Matrix W W ℂ)*ᵥf =
      (Complex.I*(1-(x : ℂ)^2)*Q.eval (x : ℂ)) • y+star (P.eval (x : ℂ)) • f := by
  induction zs with
  | nil =>
    simp [unitaryPhaseWord,QSP.sequencePair,QSP.phase,hΦy,hΦf,← Circle.coe_inv_eq_conj]
  | cons z zs ih =>
    dsimp only [unitaryPhaseWord,QSP.sequencePair] at *
    have hz : star (z : ℂ) = ((z⁻¹ : Circle) : ℂ) := (Circle.coe_inv_eq_conj z).symm
    have hzi : star ((z⁻¹ : Circle) : ℂ) = (z : ℂ) := by simpa using (Circle.coe_inv_eq_conj z⁻¹).symm
    constructor
    all_goals
      change (((unitaryPhaseWord S Φ z₀ zs : Matrix W W ℂ)*(S : Matrix W W ℂ))*(Φ z : Matrix W W ℂ))*ᵥ_ = _
      simp only [← Matrix.mulVec_mulVec,hΦy,hΦf,Matrix.mulVec_smul,hSy,hSf,Matrix.mulVec_add,
        ih.1,ih.2,QSP.forwardP,QSP.forwardQ,QSP.phase,eval_mul,eval_add,eval_sub,eval_pow,
        eval_X,eval_C,eval_one,map_add,map_sub,map_mul,map_pow,star_one,star_natCast,
        Complex.conj_ofReal,hz,hzi]
      ext w
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      ring_nf
      simp [Complex.I_sq,← Circle.coe_inv_eq_conj,Circle.coe_inv]
      ring

/-- The actual QSP word on the oracle workspace. -/
def hermitianPhaseWord (E : Matrix W D ℂ) (hE : Eᴴ*E=1)
    (U : Matrix.unitaryGroup W ℂ) (z₀ : Circle) (zs : List Circle) :
    Matrix.unitaryGroup W ℂ :=
  unitaryPhaseWord (hermitianSignal E hE U) (reciprocalSignalPhase E hE) z₀ zs

/-- An actual eigenvector of the encoded block acquires the synthesized
polynomial value in the selected signal block. -/
theorem hermitianPhaseWord_eigenvector (E : Matrix W D ℂ) (hE : Eᴴ*E=1)
    (U : Matrix.unitaryGroup W ℂ) (hU : (U : Matrix W W ℂ)ᴴ=U)
    (A : Matrix D D ℂ) (hblock : Eᴴ*(U : Matrix W W ℂ)*E=A)
    (v : D → ℂ) (x : ℝ) (hAv : A*ᵥv=(x : ℂ) • v)
    (z₀ : Circle) (zs : List Circle) :
    (Eᴴ*(hermitianPhaseWord E hE U z₀ zs : Matrix W W ℂ)*E)*ᵥv =
      (QSP.sequencePair z₀ zs).1.eval (x : ℂ) • v := by
  let F := signalLeakage E U A
  let y := E*ᵥv
  let f := F*ᵥv
  let S := hermitianSignal E hE U
  let Φ := reciprocalSignalPhase E hE
  have hF : Eᴴ*F=0 := signalLeakage_orthogonal E hE U A hblock
  have hcols := hermitianSignal_columns E hE U hU A hblock
  have hSy : (S : Matrix W W ℂ)*ᵥy=(x : ℂ) • y+Complex.I • f := by
    change (S : Matrix W W ℂ)*ᵥ(E*ᵥv) = _
    rw [Matrix.mulVec_mulVec,hcols.1]
    simp only [Matrix.add_mulVec,Matrix.smul_mulVec,← Matrix.mulVec_mulVec,hAv,Matrix.mulVec_smul]
    rfl
  have hSf : (S : Matrix W W ℂ)*ᵥf=(Complex.I*(1-(x : ℂ)^2)) • y+(x : ℂ) • f := by
    change (S : Matrix W W ℂ)*ᵥ(F*ᵥv) = _
    rw [Matrix.mulVec_mulVec,hcols.2]
    simp only [Matrix.add_mulVec,Matrix.smul_mulVec,← Matrix.mulVec_mulVec,
      Matrix.sub_mulVec,Matrix.one_mulVec,hAv,Matrix.mulVec_smul,Matrix.mulVec_sub]
    dsimp only [y,f]
    module
  have hΦy : ∀ z, (Φ z : Matrix W W ℂ)*ᵥy=(z : ℂ) • y := by
    intro z
    change (insertionPhases E hE z z⁻¹ : Matrix W W ℂ)*ᵥ(E*ᵥv)=_
    rw [Matrix.mulVec_mulVec,insertionPhases_mul_E,Matrix.smul_mulVec]
  have hΦf : ∀ z, (Φ z : Matrix W W ℂ)*ᵥf=((z⁻¹ : Circle) : ℂ) • f := by
    intro z
    change (insertionPhases E hE z z⁻¹ : Matrix W W ℂ)*ᵥ(F*ᵥv)=_
    rw [Matrix.mulVec_mulVec,insertionPhases_mul_orthogonal E F hE hF,Matrix.smul_mulVec]
  have ha := (unitaryPhaseWord_pair_action S Φ y f x hSy hSf hΦy hΦf z₀ zs).1
  have hy : Eᴴ*ᵥy=v := by dsimp only [y]; rw [Matrix.mulVec_mulVec,hE,Matrix.one_mulVec]
  have hf : Eᴴ*ᵥf=0 := by dsimp only [f]; rw [Matrix.mulVec_mulVec,hF,Matrix.zero_mulVec]
  change (Eᴴ*(unitaryPhaseWord S Φ z₀ zs : Matrix W W ℂ)*E)*ᵥv=_
  simp only [← Matrix.mulVec_mulVec]
  change Eᴴ*ᵥ((unitaryPhaseWord S Φ z₀ zs : Matrix W W ℂ)*ᵥy)=_
  rw [ha,Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_smul,hy,hf,smul_zero,add_zero]

/-- Literal matrix polynomial evaluation on an actual eigenvector. -/
theorem matrix_polynomial_eigenvector (A : Matrix D D ℂ) (p : ℂ[X])
    (v : D → ℂ) (lam : ℂ) (hv : A*ᵥv=lam • v) :
    (Polynomial.aeval A p)*ᵥv=p.eval lam • v := by
  have hpow : ∀ n : ℕ, (A^n)*ᵥv=lam^n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ',← Matrix.mulVec_mulVec,ih,Matrix.mulVec_smul,hv,smul_smul,pow_succ]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp,hq,Matrix.add_mulVec,add_smul]
  | monomial n c =>
    rw [Polynomial.aeval_monomial,Algebra.algebraMap_eq_smul_one,← Matrix.mulVec_mulVec,
      hpow,Matrix.smul_mulVec,Matrix.one_mulVec,smul_smul,eval_monomial]

/-- General matrix-level realization for a Hermitian unitary oracle: the
literal selected block is the polynomial evaluated on the actual matrix A. -/
theorem hermitianPhaseWord_compression (E : Matrix W D ℂ) (hE : Eᴴ*E=1)
    (U : Matrix.unitaryGroup W ℂ) (hU : (U : Matrix W W ℂ)ᴴ=U)
    (A : Matrix D D ℂ) (hA : A.IsHermitian) (hblock : Eᴴ*(U : Matrix W W ℂ)*E=A)
    (z₀ : Circle) (zs : List Circle) :
    Eᴴ*(hermitianPhaseWord E hE U z₀ zs : Matrix W W ℂ)*E =
      Polynomial.aeval A (QSP.sequencePair z₀ zs).1 := by
  apply Matrix.toEuclideanLin.injective
  apply hA.eigenvectorBasis.toBasis.ext
  intro i
  have heig : A*ᵥ⇑(hA.eigenvectorBasis i)=
      (hA.eigenvalues i : ℂ) • ⇑(hA.eigenvectorBasis i) := by
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ)] using hA.mulVec_eigenvectorBasis i
  change WithLp.toLp 2 ((Eᴴ*(hermitianPhaseWord E hE U z₀ zs : Matrix W W ℂ)*E)*ᵥ
      ⇑(hA.eigenvectorBasis i)) =
    WithLp.toLp 2 ((Polynomial.aeval A (QSP.sequencePair z₀ zs).1)*ᵥ⇑(hA.eigenvectorBasis i))
  rw [hermitianPhaseWord_eigenvector E hE U hU A hblock _ _ heig,
    matrix_polynomial_eigenvector A _ _ _ heig]


end OptimalQLS.PolynomialTransform
