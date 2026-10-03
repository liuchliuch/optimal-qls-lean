import OptimalQLS.PolynomialTransform.RealCompletion
import OptimalQLS.PolynomialTransform.QSPUnitary

/-! # Constructive QSP realization of bounded even real polynomials -/
noncomputable section
namespace OptimalQLS.PolynomialTransform
open Polynomial
open scoped ComplexConjugate

/-- Functional evenness implies the actual coefficient-support parity. -/
theorem even_polynomial_parity (p : ℝ[X]) (hp : Function.Even p.eval) : Completion.Parity p 0 := by
  have he : p.comp (C (-1)*X) = p := by
    apply Polynomial.funext
    intro x
    simpa using hp x
  intro n hn
  have hodd : n % 2 = 1 := by omega
  have hc := congrArg (fun q : ℝ[X] => q.coeff n) he
  dsimp only at hc
  rw [comp_C_mul_X_coeff, neg_one_pow_eq_pow_mod_two, hodd] at hc
  norm_num at hc
  linarith

def liftReal (p : ℝ[X]) : ℂ[X] := p.map (algebraMap ℝ ℂ)

@[simp] theorem liftReal_zero : liftReal 0 = 0 := by simp [liftReal]
@[simp] theorem liftReal_one : liftReal 1 = 1 := by simp [liftReal]
@[simp] theorem liftReal_X : liftReal X = X := by simp [liftReal]
@[simp] theorem liftReal_add (p q : ℝ[X]) : liftReal (p+q) = liftReal p+liftReal q := by simp [liftReal]
@[simp] theorem liftReal_sub (p q : ℝ[X]) : liftReal (p-q) = liftReal p-liftReal q := by simp [liftReal]
@[simp] theorem liftReal_mul (p q : ℝ[X]) : liftReal (p*q) = liftReal p*liftReal q := by simp [liftReal]
@[simp] theorem liftReal_pow (p : ℝ[X]) (n : ℕ) : liftReal (p^n) = liftReal p^n := by simp [liftReal]
@[simp] theorem liftReal_natDegree (p : ℝ[X]) : (liftReal p).natDegree = p.natDegree := by
  exact Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective p
@[simp] theorem liftReal_eval (p : ℝ[X]) (x : ℝ) :
    (liftReal p).eval (x : ℂ) = ((p.eval x : ℝ) : ℂ) := by
  exact eval_map_apply (algebraMap ℝ ℂ) x
@[simp] theorem conjugate_liftReal (p : ℝ[X]) : QSP.conjugate (liftReal p) = liftReal p := by
  ext n
  simp [QSP.conjugate_coeff, liftReal]

theorem liftReal_parity {p : ℝ[X]} {n : ℕ} (hp : Completion.Parity p n) :
    QSP.HasParity (liftReal p) n := by
  intro k hk
  simp [liftReal, hp k hk]

/-- The completed complex primary and secondary polynomials. -/
def completedP (p B : ℝ[X]) : ℂ[X] := liftReal p + C Complex.I * liftReal B
def completedQ (C₀ : ℝ[X]) : ℂ[X] := C Complex.I * liftReal C₀

/-- A proved weighted sum-of-squares completion produces exact normalization. -/
theorem completion_normalizes (p B C₀ : ℝ[X])
    (h : 1-p^2 = Completion.weightedNorm B C₀) :
    QSP.normPolynomial (completedP p B) (completedQ C₀) = 1 := by
  have hm := congrArg liftReal h
  simp only [Completion.weightedNorm, liftReal_sub, liftReal_one, liftReal_pow,
    liftReal_add, liftReal_mul, liftReal_X] at hm
  have hi : (C Complex.I : ℂ[X])^2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  calc
    QSP.normPolynomial (completedP p B) (completedQ C₀) =
        (liftReal p)^2+(liftReal B)^2+(1-X^2)*(liftReal C₀)^2 := by
      simp only [QSP.normPolynomial, completedP, completedQ, QSP.conjugate_add,
        QSP.conjugate_mul, conjugate_liftReal, QSP.conjugate_C, RCLike.star_def,
        Complex.conj_I, map_neg]
      ring_nf
      rw [hi]
      ring
    _ = 1 := by linear_combination -hm

/-- The real part is the requested real polynomial exactly, not up to error. -/
@[simp] theorem completedP_realPart (p B : ℝ[X]) (x : ℝ) :
    ((completedP p B).eval (x : ℂ)).re = p.eval x := by
  simp [completedP, liftReal_eval]

/-- Bounded real even p is completed constructively into a normalized complex
pair, with an explicit degree bound and parity. -/
theorem bounded_even_completion (p : ℝ[X]) (hp : Function.Even p.eval)
    (hbound : ∀ x : ℝ, |x| ≤ 1 → |p.eval x| ≤ 1) :
    ∃ B C₀ : ℝ[X],
      QSP.normPolynomial (completedP p B) (completedQ C₀) = 1 ∧
      (completedP p B).natDegree ≤ p.natDegree ∧
      QSP.HasParity (completedP p B) p.natDegree ∧
      QSP.HasParity (completedQ C₀) (p.natDegree+1) := by
  have hp0 := even_polynomial_parity p hp
  have hpdeg : Completion.Parity p p.natDegree := by
    by_cases h0 : p = 0
    · subst p
      exact Completion.parity_zero _
    have hm : p.natDegree % 2 = 0 := by
      by_contra hn
      exact (leadingCoeff_ne_zero.mpr h0) (hp0 p.natDegree (by simpa using hn))
    exact hp0.congr hm.symm
  have hApar : Completion.Parity (1-p^2) 0 := by
    have h1 : Completion.Parity (1 : ℝ[X]) 0 := by simpa using Completion.parity_C 1
    apply h1.sub
    simpa [pow_two] using hp0.mul hp0
  have hAdeg : (1-p^2).natDegree ≤ 2*p.natDegree := by
    apply (natDegree_sub_le _ _).trans
    simp only [natDegree_one, Nat.zero_max, natDegree_pow]
    rfl
  have hAnon : ∀ x : ℝ, |x| ≤ 1 → 0 ≤ (1-p^2).eval x := by
    intro x hx
    have hb := hbound x hx
    simp only [eval_sub, eval_one, eval_pow]
    nlinarith [sq_abs (p.eval x), abs_nonneg (p.eval x)]
  obtain ⟨B,C₀,hcomp,hB,hC,hBp,hCp⟩ :=
    Completion.lemma6_real_completion (1-p^2) p.natDegree hApar hAdeg hAnon
  refine ⟨B,C₀,completion_normalizes p B C₀ hcomp,?_,?_,?_⟩
  · apply (natDegree_add_le _ _).trans
    apply max_le
    · simp
    · exact (natDegree_C_mul_le _ _).trans (by simpa using hB)
  · exact (liftReal_parity hpdeg).add ((liftReal_parity hBp).C_mul _)
  · exact (liftReal_parity hCp).C_mul _

/-- Uniform phases are chosen from p alone, before any matrix oracle is given. -/
theorem bounded_even_phase_synthesis (p : ℝ[X]) (hp : Function.Even p.eval)
    (hbound : ∀ x : ℝ, |x| ≤ 1 → |p.eval x| ≤ 1) :
    ∃ (B C₀ : ℝ[X]) (z₀ : Circle) (zs : List Circle),
      QSP.sequencePair z₀ zs=(completedP p B,completedQ C₀) ∧ zs.length ≤ p.natDegree := by
  obtain ⟨B,C₀,hN,hdeg,hPpar,hQpar⟩ := bounded_even_completion p hp hbound
  have hmod := hPpar.natDegree (QSP.normalized_P_ne_zero hN)
  obtain ⟨z₀,zs,hseq,hlen⟩ := QSP.normalized_pair_factorization (completedP p B) (completedQ C₀)
    hN (hPpar.congr hmod.symm) (hQpar.congr (by omega))
  exact ⟨B,C₀,z₀,zs,hseq,hlen.trans hdeg⟩

/-- The real-even-polynomial QSP theorem, including actual unitary products.
The number of signal rotations is at most the polynomial's degree. All
existential phases come from the proved completion and factorization. -/
theorem bounded_even_real_qsp (p : ℝ[X]) (hp : Function.Even p.eval)
    (hbound : ∀ x : ℝ, |x| ≤ 1 → |p.eval x| ≤ 1) :
    ∃ (z₀ : Circle) (zs : List Circle), zs.length ≤ p.natDegree ∧
      ∀ (x : ℝ) (hx : |x| ≤ 1),
        (((QSP.scalarSequence x hx z₀ zs : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re) = p.eval x := by
  obtain ⟨B,C₀,hN,hdeg,hPpar,hQpar⟩ := bounded_even_completion p hp hbound
  have hmod := hPpar.natDegree (QSP.normalized_P_ne_zero hN)
  have hPpar' : QSP.HasParity (completedP p B) (completedP p B).natDegree :=
    hPpar.congr hmod.symm
  have hQpar' : QSP.HasParity (completedQ C₀) ((completedP p B).natDegree+1) :=
    hQpar.congr (by omega)
  obtain ⟨z₀,zs,hlen,hmat⟩ := QSP.normalized_pair_unitary_realization
    (completedP p B) (completedQ C₀) hN hPpar' hQpar'
  refine ⟨z₀,zs,hlen.trans hdeg,?_⟩
  intro x hx
  rw [hmat]
  simpa [QSP.pairMatrix] using completedP_realPart p B x

end OptimalQLS.PolynomialTransform
