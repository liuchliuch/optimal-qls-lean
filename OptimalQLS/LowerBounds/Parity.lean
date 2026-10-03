import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic

/-!
# Parity orthogonality on the actual Boolean cube

This proves the sign-degree obstruction used in Section 6 without assuming
any polynomial-method or query-lower-bound theorem. It applies to ordinary
(not necessarily multilinear) complex polynomials.
-/
noncomputable section
open scoped BigOperators
namespace OptimalQLS.LowerBounds
open MvPolynomial

abbrev BitString (m : ℕ) := Fin m → Bool

def bitValue {m : ℕ} (z : BitString m) (i : Fin m) : ℂ :=
  if z i then 1 else 0

def paritySign {m : ℕ} (z : BitString m) : ℝ :=
  ∏ i, if z i then -1 else 1

def flipInput {m : ℕ} (i : Fin m) (z : BitString m) : BitString m :=
  Function.update z i (!(z i))

@[simp] theorem flipInput_self {m : ℕ} (i : Fin m) (z : BitString m) :
    flipInput i z i = !(z i) := by simp [flipInput]

@[simp] theorem flipInput_other {m : ℕ} (i j : Fin m) (h : j ≠ i) (z : BitString m) :
    flipInput i z j = z j := by simp [flipInput, h]

@[simp] theorem flipInput_involutive {m : ℕ} (i : Fin m) :
    Function.Involutive (flipInput i) := by
  intro z
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [h]

def flipInputEquiv {m : ℕ} (i : Fin m) : BitString m ≃ BitString m :=
  (flipInput_involutive i).toPerm

@[simp] theorem paritySign_flip {m : ℕ} (i : Fin m) (z : BitString m) :
    paritySign (flipInput i z) = -paritySign z := by
  classical
  unfold paritySign
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ i),
      Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ i)]
  have hrest :
      (∏ j ∈ Finset.univ \ {i}, if flipInput i z j then (-1 : ℝ) else 1) =
      ∏ j ∈ Finset.univ \ {i}, if z j then (-1 : ℝ) else 1 := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := by simpa using (Finset.mem_sdiff.mp hj).2
    simp [hji]
  rw [hrest]
  cases hz : z i <;> simp [hz]

def parityCoefficient {m : ℕ} (p : MvPolynomial (Fin m) ℂ) : ℂ :=
  ∑ z : BitString m, (paritySign z : ℂ) * eval (bitValue z) p

theorem eval_monomial_flip_of_missing {m : ℕ} (i : Fin m)
    (d : Fin m →₀ ℕ) (hd : d i = 0) (a : ℂ) (z : BitString m) :
    eval (bitValue (flipInput i z)) (monomial d a) =
      eval (bitValue z) (monomial d a) := by
  classical
  simp only [eval_monomial]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := by
    intro h; subst j
    exact (Finsupp.mem_support_iff.mp hj) hd
  simp [bitValue, hji]

theorem parityCoefficient_monomial_of_missing {m : ℕ} (i : Fin m)
    (d : Fin m →₀ ℕ) (hd : d i = 0) (a : ℂ) :
    parityCoefficient (monomial d a) = 0 := by
  classical
  have hreindex := (flipInputEquiv i).sum_comp
    (fun z : BitString m => (paritySign z : ℂ) * eval (bitValue z) (monomial d a))
  have hneg : parityCoefficient (monomial d a) =
      -parityCoefficient (monomial d a) := by
    calc
      parityCoefficient (monomial d a) =
          ∑ z : BitString m, (paritySign (flipInput i z) : ℂ) *
            eval (bitValue (flipInput i z)) (monomial d a) := hreindex.symm
      _ = -parityCoefficient (monomial d a) := by
        simp [paritySign_flip, eval_monomial_flip_of_missing i d hd, parityCoefficient,
          ← Finset.sum_neg_distrib]
  linear_combination (1 / 2 : ℂ) * hneg

/-- A polynomial of total degree below the number of input bits has zero
full-parity Fourier coefficient. No multilinearization premise is needed. -/
theorem parityCoefficient_eq_zero_of_degree_lt {m : ℕ}
    (p : MvPolynomial (Fin m) ℂ) (hdeg : p.totalDegree < m) :
    parityCoefficient p = 0 := by
  classical
  have hm : p.totalDegree < 1 * Fintype.card (Fin m) := by simpa using hdeg
  have hz : ∀ d ∈ p.support, parityCoefficient (monomial d (coeff d p)) = 0 := by
    intro d hd
    obtain ⟨i, hi⟩ := exists_degree_lt p 1 hm hd
    exact parityCoefficient_monomial_of_missing i d (by omega) _
  conv_lhs => rw [p.as_sum]
  simp only [parityCoefficient, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero (fun d hd => hz d hd)

/-- Strict pointwise agreement with parity forces degree at least `m`.
The real part permits complex polynomial coefficients and therefore connects
directly to complex quantum amplitudes. -/
theorem degree_ge_of_strict_parity_sign {m : ℕ} (p : MvPolynomial (Fin m) ℂ)
    (h : ∀ z : BitString m, 0 < paritySign z * (eval (bitValue z) p).re) :
    m ≤ p.totalDegree := by
  classical
  by_contra hn
  have hz := parityCoefficient_eq_zero_of_degree_lt p (by omega)
  have hp : 0 < (parityCoefficient p).re := by
    simp only [parityCoefficient, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    exact Finset.sum_pos (fun z _ => h z) Finset.univ_nonempty
  simpa [hz] using hp

end OptimalQLS.LowerBounds
