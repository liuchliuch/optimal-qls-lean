import OptimalQLS.PolynomialTransform.QSPFactorization
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Constructive real polynomial completion on an interval

The weighted sum-of-two-squares construction used by GSLW Lemma 6 is
assembled from actual polynomial factors. This file does not assume a
bounded-polynomial completion theorem.
-/
noncomputable section
namespace OptimalQLS.PolynomialTransform.Completion
open Polynomial

/-- Real coefficient-support parity. -/
def Parity (P : ℝ[X]) (k : ℕ) : Prop := ∀ n, n % 2 ≠ k % 2 → P.coeff n = 0

theorem Parity.congr {P : ℝ[X]} {k j : ℕ} (hP : Parity P k) (h : k % 2 = j % 2) :
    Parity P j := fun n hn => hP n (by simpa [h] using hn)

theorem parity_zero (k : ℕ) : Parity 0 k := by intro n hn; simp

theorem parity_C (c : ℝ) : Parity (C c) 0 := by
  intro n hn
  have hn0 : n ≠ 0 := by intro h; simp [h] at hn
  simp [coeff_C, hn0]

theorem parity_X : Parity (X : ℝ[X]) 1 := by
  intro n hn
  have hn1 : n ≠ 1 := by intro h; simp [h] at hn
  simp [coeff_X, Ne.symm hn1]

theorem Parity.add {P Q : ℝ[X]} {k : ℕ} (hP : Parity P k) (hQ : Parity Q k) :
    Parity (P + Q) k := by intro n hn; simp [hP n hn, hQ n hn]

theorem Parity.sub {P Q : ℝ[X]} {k : ℕ} (hP : Parity P k) (hQ : Parity Q k) :
    Parity (P - Q) k := by intro n hn; simp [hP n hn, hQ n hn]

theorem Parity.mul {P Q : ℝ[X]} {k j : ℕ} (hP : Parity P k) (hQ : Parity Q j) :
    Parity (P * Q) (k + j) := by
  intro n hn
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ab hab
  have hab' : ab.1 + ab.2 = n := Finset.mem_antidiagonal.mp hab
  by_cases ha : ab.1 % 2 = k % 2
  · have hb : ab.2 % 2 ≠ j % 2 := by omega
    rw [hQ ab.2 hb, mul_zero]
  · rw [hP ab.1 ha, zero_mul]

theorem parity_X_sq : Parity (X ^ 2 : ℝ[X]) 0 := by
  simpa [pow_two] using (parity_X.mul parity_X).congr (by norm_num : (1 + 1) % 2 = 0 % 2)

theorem Parity.C_mul {P : ℝ[X]} {k : ℕ} (hP : Parity P k) (c : ℝ) :
    Parity (C c * P) k := by simpa using (parity_C c).mul hP

/-- Weighted norm B²+(1-X²)C². -/
def weightedNorm (B C : ℝ[X]) : ℝ[X] := B^2 + (1-X^2)*C^2

/-- Exact multiplicative closure of the weighted norm. -/
theorem weightedNorm_mul (B C D E : ℝ[X]) :
    weightedNorm (B*D-(1-X^2)*C*E) (B*E+C*D) = weightedNorm B C * weightedNorm D E := by
  unfold weightedNorm
  ring

/-- A completion with explicit degree and coefficient parity. This predicate
states the desired algebraic witnesses; its instances below are constructed. -/
def HasCompletion (A : ℝ[X]) (k : ℕ) : Prop :=
  ∃ B C : ℝ[X], A.comp (X^2) = weightedNorm B C ∧ B.natDegree ≤ k ∧
    (C = 0 ∨ C.natDegree < k) ∧ Parity B k ∧ Parity C (k+1)

theorem completion_zero : HasCompletion 0 0 := by
  refine ⟨0, 0, by simp [weightedNorm], by simp, Or.inl rfl, parity_zero _, parity_zero _⟩

theorem completion_constant (a : ℝ) (ha : 0 ≤ a) : HasCompletion (C a) 0 := by
  refine ⟨C (Real.sqrt a), 0, ?_, by simp, Or.inl rfl, parity_C _, parity_zero _⟩
  simp [weightedNorm, ← map_pow, Real.sq_sqrt ha]

/-- A linear factor nonnegative to the left of the interval. -/
theorem completion_linear_below (r : ℝ) (hr : r ≤ 0) : HasCompletion (X-C r) 1 := by
  refine ⟨C (Real.sqrt (1-r))*X, C (Real.sqrt (-r)), ?_, ?_, Or.inr (by simp), ?_, ?_⟩
  · simp only [sub_comp, X_comp, C_comp, weightedNorm, mul_pow, ← map_pow]
    rw [Real.sq_sqrt (by linarith : 0 ≤ 1-r), Real.sq_sqrt (by linarith : 0 ≤ -r)]
    simp only [map_sub, map_one, map_neg]
    ring
  · exact (natDegree_C_mul_le _ _).trans (by simp)
  · exact parity_X.C_mul _
  · exact (parity_C _).congr (by norm_num)

/-- A linear factor nonnegative to the right of the interval. -/
theorem completion_linear_above (r : ℝ) (hr : 1 ≤ r) : HasCompletion (C r-X) 1 := by
  refine ⟨C (Real.sqrt (r-1))*X, C (Real.sqrt r), ?_, ?_, Or.inr (by simp), ?_, ?_⟩
  · simp only [sub_comp, X_comp, C_comp, weightedNorm, mul_pow, ← map_pow]
    rw [Real.sq_sqrt (by linarith : 0 ≤ r-1), Real.sq_sqrt (by linarith : 0 ≤ r)]
    simp only [map_sub, map_one]
    ring
  · exact (natDegree_C_mul_le _ _).trans (by simp)
  · exact parity_X.C_mul _
  · exact (parity_C _).congr (by norm_num)

/-- An interior root is removed in pairs; its squared factor has this completion. -/
theorem completion_linear_square (r : ℝ) : HasCompletion ((X-C r)^2) 2 := by
  refine ⟨X^2-C r, 0, by simp [weightedNorm], ?_, Or.inl rfl, ?_, parity_zero _⟩
  · exact (natDegree_sub_le _ _).trans (by simp)
  · exact (parity_X_sq.sub (parity_C r)).congr (by norm_num)

/-- Degree and parity bookkeeping for multiplication of completed factors. -/
theorem HasCompletion.mul {A D : ℝ[X]} {k j : ℕ}
    (hA : HasCompletion A k) (hD : HasCompletion D j) : HasCompletion (A*D) (k+j) := by
  obtain ⟨B,C,hA,hB,hC,hBp,hCp⟩ := hA
  obtain ⟨F,G,hD,hF,hG,hFp,hGp⟩ := hD
  refine ⟨B*F-(1-X^2)*C*G, B*G+C*F, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mul_comp, hA, hD, weightedNorm_mul]
  · have hBF : (B*F).natDegree ≤ k+j := natDegree_mul_le.trans (by omega)
    rcases hC with rfl | hC
    · simpa using hBF
    rcases hG with rfl | hG
    · simpa using hBF
    have hf : (1-X^2 : ℝ[X]).natDegree ≤ 2 := (natDegree_sub_le _ _).trans (by simp)
    have ht : ((1-X^2)*C*G).natDegree ≤ k+j := by
      have h₁ := natDegree_mul_le (p := (1-X^2 : ℝ[X])) (q := C)
      have h₂ := natDegree_mul_le (p := (1-X^2)*C) (q := G)
      omega
    exact (natDegree_sub_le _ _).trans (max_le hBF ht)
  · by_cases hz : B*G+C*F = 0
    · exact Or.inl hz
    right
    have hpos : 0 < k+j := by
      by_contra hn
      have hk : k = 0 := by omega
      have hj : j = 0 := by omega
      have hC0 : C = 0 := hC.resolve_right (by omega)
      have hG0 : G = 0 := hG.resolve_right (by omega)
      simp [hC0, hG0] at hz
    have hBG : (B*G).natDegree < k+j := by
      rcases hG with rfl | hG
      · simpa using hpos
      exact natDegree_mul_le.trans_lt (by omega)
    have hCF : (C*F).natDegree < k+j := by
      rcases hC with rfl | hC
      · simpa using hpos
      exact natDegree_mul_le.trans_lt (by omega)
    exact (natDegree_add_le _ _).trans_lt (max_lt hBG hCF)
  · have hweight : Parity (1-X^2 : ℝ[X]) 0 := by
      have h1 : Parity (1 : ℝ[X]) 0 := by simpa using parity_C 1
      exact h1.sub parity_X_sq
    exact (hBp.mul hFp).sub ((hweight.mul hCp).mul hGp |>.congr (by omega))
  · exact (hBp.mul hGp).add ((hCp.mul hFp).congr (by omega))

/-- The real quadratic factor of a conjugate pair has an explicit completion. -/
theorem completion_complex_quadratic (z : ℂ) :
    HasCompletion (X^2-C (2*z.re)*X+C (‖z‖^2)) 2 := by
  let d : ℝ := ‖z‖
  let s : ℝ := ‖z-1‖
  let c : ℝ := d+s
  have hc : 1 ≤ c := by
    have h := norm_add_le z (1-z)
    simpa [c, d, s, norm_sub_rev, show z+(1-z)=1 by ring] using h
  have hsq : s^2 = d^2-2*z.re+1 := by
    dsimp only [s,d]
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
    ring
  have hcq : c^2-2*c*d-1 = -(2*z.re) := by dsimp only [c]; nlinarith
  let e := Real.sqrt (c^2-1)
  have he : e^2 = c^2-1 := Real.sq_sqrt (by nlinarith)
  refine ⟨C c*X^2-C d, C e*X, ?_, ?_, Or.inr ?_, ?_, ?_⟩
  · simp only [sub_comp, add_comp, mul_comp, pow_comp, X_comp, C_comp]
    calc
      (X^2)^2-C (2*z.re)*X^2+C (‖z‖^2) =
          C (c^2-e^2)*X^4+C (e^2-2*c*d)*X^2+C (d^2) := by
        rw [he, show c^2-(c^2-1)=1 by ring, show c^2-1-2*c*d=-(2*z.re) by linarith [hcq]]
        simp only [map_one, one_mul, map_neg]
        dsimp only [d]
        ring
      _ = weightedNorm (C c*X^2-C d) (C e*X) := by
        simp only [weightedNorm, map_sub, map_mul, map_pow, map_ofNat]
        ring
  · apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact (natDegree_C_mul_le _ _).trans (by simp)
    · simp
  · exact (natDegree_C_mul_le _ _).trans_lt (by simp)
  · exact ((parity_X_sq.C_mul c).sub (parity_C d)).congr (by norm_num)
  · exact (parity_X.C_mul e).congr (by norm_num)

/-- Continuity fills a single excluded point of a nonnegativity argument. -/
theorem nonneg_on_Icc_of_off_point (P : ℝ[X]) (r : ℝ)
    (hP : ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≠ r → 0 ≤ P.eval x) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ P.eval x := by
  intro x hx
  by_cases hxr : x = r
  · subst x
    have hc : IsClosed {y : ℝ | 0 ≤ P.eval y} := isClosed_le continuous_const P.continuous
    by_cases hr : 0 < r
    · have hs : Set.Ioo 0 r ⊆ {y : ℝ | 0 ≤ P.eval y} := by
        intro y hy
        exact hP y ⟨hy.1.le, hy.2.le.trans hx.2⟩ hy.2.ne
      apply (closure_minimal hs hc)
      rw [closure_Ioo hr.ne]
      exact ⟨hr.le, le_rfl⟩
    · have hr0 : r = 0 := by linarith [hx.1]
      have hs : Set.Ioo (0 : ℝ) 1 ⊆ {y : ℝ | 0 ≤ P.eval y} := by
        intro y hy
        exact hP y ⟨hy.1.le, hy.2.le⟩ (by rw [hr0]; exact hy.1.ne')
      apply (closure_minimal hs hc)
      rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), hr0]
      exact ⟨le_rfl, by norm_num⟩
  · exact hP x hx hxr

/-- An interior root of a nonnegative real polynomial is at least double,
derived by Fermat's theorem rather than assumed root multiplicity. -/
theorem interior_root_square_dvd (A : ℝ[X]) (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hA : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ A.eval x) (hroot : A.eval r = 0) :
    (X-C r)^2 ∣ A := by
  have hlocal : IsLocalMin A.eval r := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with x hx
    rw [hroot]
    exact hA x ⟨hx.1.le,hx.2.le⟩
  have hd : A.derivative.eval r = 0 := hlocal.hasDerivAt_eq_zero (A.hasDerivAt r)
  obtain ⟨Q,hQ⟩ := (dvd_iff_isRoot.mpr hroot : X-C r ∣ A)
  have hQr : Q.eval r = 0 := by
    rw [hQ] at hd
    simpa using hd
  obtain ⟨R,hR⟩ := (dvd_iff_isRoot.mpr hQr : X-C r ∣ Q)
  exact ⟨R, by rw [hQ,hR]; ring⟩

/-- Removing the squared interior factor preserves nonnegativity on the
whole closed interval, including at the removed root. -/
theorem interior_square_quotient_nonneg (A R : ℝ[X]) (r : ℝ)
    (hA : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ A.eval x)
    (hfactor : A = (X-C r)^2 * R) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ R.eval x := by
  apply nonneg_on_Icc_of_off_point R r
  intro x hx hxr
  have h := hA x hx
  rw [hfactor] at h
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C] at h
  exact nonneg_of_mul_nonneg_right h (sq_pos_of_ne_zero (sub_ne_zero.mpr hxr))


/-- Exact monic normalization of a real quadratic factor. -/
theorem real_quadratic_monic (b c : ℝ) : (X^2-C b*X+C c : ℝ[X]).Monic := by
  have heq : (X^2-C b*X+C c : ℝ[X]) = C 1*X^2+C (-b)*X+C c := by simp; ring
  rw [heq]
  change (C 1*X^2+C (-b)*X+C c : ℝ[X]).leadingCoeff = 1
  rw [Polynomial.leadingCoeff, natDegree_quadratic (by norm_num : (1 : ℝ) ≠ 0)]
  simp

theorem real_quadratic_natDegree (b c : ℝ) : (X^2-C b*X+C c : ℝ[X]).natDegree = 2 := by
  have heq : (X^2-C b*X+C c : ℝ[X]) = C 1*X^2+C (-b)*X+C c := by simp; ring
  rw [heq, natDegree_quadratic (by norm_num : (1 : ℝ) ≠ 0)]

/-- A monic irreducible real quadratic is the explicit conjugate-root
quadratic, which is strictly positive at every real argument. -/
theorem irreducible_quadratic_form (q : ℝ[X]) (hm : q.Monic) (hi : Irreducible q)
    (hd : q.natDegree = 2) :
    ∃ z : ℂ, z.im ≠ 0 ∧ q = X^2-C (2*z.re)*X+C (‖z‖^2) ∧
      ∀ x : ℝ, 0 < q.eval x := by
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ q (degree_pos_of_irreducible hi).ne'
  have him : z.im ≠ 0 := by
    intro hz0
    have hzr : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz0]
    rw [hzr] at hz
    have hzreal : q.eval z.re = 0 := by
      have he := aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) z.re q
      have hc : ((q.eval z.re : ℝ) : ℂ) = 0 := he.symm.trans hz
      exact_mod_cast hc
    exact hi.not_isRoot_of_natDegree_ne_one (by omega) hzreal
  have hdvd := q.quadratic_dvd_of_aeval_eq_zero_im_ne_zero hz him
  have hform : q = X^2-C (2*z.re)*X+C (‖z‖^2) :=
    eq_of_monic_of_dvd_of_natDegree_le (real_quadratic_monic _ _) hm hdvd
      (by rw [hd, real_quadratic_natDegree])
  refine ⟨z,him,hform,?_⟩
  intro x
  rw [hform]
  simp only [eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C]
  have hs : ‖z‖^2 = z.re^2+z.im^2 := by rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  rw [hs]
  nlinarith [sq_pos_of_ne_zero him, sq_nonneg (x-z.re)]

/-- Constructive interval completion by irreducible-factor induction.
Every factor is actually built; positivity is used to handle interior roots
in pairs, and to preserve positivity of the remaining quotient. -/
theorem interval_completion (A : ℝ[X])
    (hA : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ A.eval x) : HasCompletion A A.natDegree := by
  generalize hn : A.natDegree = n
  induction n using Nat.strong_induction_on generalizing A with
  | h n ih =>
    by_cases hz : A = 0
    · subst A
      simp only [natDegree_zero] at hn
      subst n
      exact completion_zero
    by_cases hd0 : A.natDegree = 0
    · have hAc : A = C (A.coeff 0) := eq_C_of_natDegree_eq_zero hd0
      have hc : 0 ≤ A.coeff 0 := by
        have hh := hA 0 ⟨le_rfl,by norm_num⟩
        rw [hAc, eval_C] at hh
        exact hh
      have hcomp := completion_constant (A.coeff 0) hc
      simpa only [← hAc, hd0, ← hn] using hcomp
    have hpos : 0 < A.natDegree := Nat.pos_of_ne_zero hd0
    obtain ⟨q,hm,hirr,R,hfactor⟩ := exists_monic_irreducible_factor A
      (not_isUnit_of_natDegree_pos A hpos)
    have hR : R ≠ 0 := by intro hR0; simp [hR0] at hfactor; exact hz hfactor
    have hqd : q.natDegree = 1 ∨ q.natDegree = 2 := by
      have hqp := hirr.natDegree_pos
      have hqu := hirr.natDegree_le_two
      omega
    have hdegree : A.natDegree = q.natDegree + R.natDegree := by
      rw [hfactor, natDegree_mul hirr.ne_zero hR]
    rcases hqd with hdq | hdq
    · let r := -q.coeff 0
      have hq : q = X-C r := by rw [hm.eq_X_add_C hdq]; simp [r]
      have hfactor' : A = (X-C r)*R := by simpa [hq] using hfactor
      have hd : A.natDegree = 1+R.natDegree := by omega
      by_cases hr0 : r ≤ 0
      · have hRn : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ R.eval x := by
          apply nonneg_on_Icc_of_off_point R r
          intro x hx hxr
          have h := hA x hx
          rw [hfactor'] at h
          simp only [eval_mul, eval_sub, eval_X, eval_C] at h
          have hstrict : 0 < x-r := by
            by_contra hn
            have he : x = r := by linarith [hx.1]
            exact hxr he
          exact nonneg_of_mul_nonneg_right h hstrict
        have hc := ih R.natDegree (by omega) R hRn rfl
        have hresult := (completion_linear_below r hr0).mul hc
        simpa only [← hfactor', ← hd, hn] using hresult
      by_cases hr1 : 1 ≤ r
      · have hRn : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ (-R).eval x := by
          apply nonneg_on_Icc_of_off_point (-R) r
          intro x hx hxr
          have h := hA x hx
          rw [hfactor'] at h
          simp only [eval_mul, eval_sub, eval_X, eval_C, eval_neg] at *
          have hneg : x-r < 0 := by
            by_contra hn
            have he : x = r := by linarith [hx.2]
            exact hxr he
          nlinarith
        have hc := ih (-R).natDegree (by simpa only [natDegree_neg] using (show R.natDegree<n by omega))
          (-R) hRn rfl
        have hfac : A = (C r-X)*(-R) := by rw [hfactor']; ring
        have hresult := (completion_linear_above r hr1).mul hc
        simpa only [natDegree_neg, ← hfac, ← hd, hn] using hresult
      · have hr : r ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_of_not_ge hr0,lt_of_not_ge hr1⟩
        have hroot : A.eval r = 0 := by simp [hfactor']
        obtain ⟨S,hS⟩ := interior_root_square_dvd A r hr hA hroot
        have hSne : S ≠ 0 := by intro h0; simp [h0] at hS; exact hz hS
        have hdS : A.natDegree = 2+S.natDegree := by
          rw [hS, natDegree_mul (pow_ne_zero 2 (X_sub_C_ne_zero r)) hSne,
            natDegree_pow, natDegree_X_sub_C]
        have hSn := interior_square_quotient_nonneg A S r hA hS
        have hc := ih S.natDegree (by omega) S hSn rfl
        have hresult := (completion_linear_square r).mul hc
        simpa only [← hS, ← hdS, hn] using hresult
    · obtain ⟨z,hzi,hq,hqpos⟩ := irreducible_quadratic_form q hm hirr hdq
      have hRn : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ R.eval x := by
        intro x hx
        have h := hA x hx
        rw [hfactor,eval_mul] at h
        exact nonneg_of_mul_nonneg_right h (hqpos x)
      have hc := ih R.natDegree (by omega) R hRn rfl
      have hresult := (completion_complex_quadratic z).mul hc
      rw [← hq] at hresult
      have hnd : 2+R.natDegree = n := by omega
      simpa only [hnd, ← hfactor] using hresult


/-- A unit weighted norm which increments the permitted degree and flips parity. -/
theorem completion_one_odd : HasCompletion (1 : ℝ[X]) 1 := by
  refine ⟨X,1,?_,by simp,Or.inr (by simp),parity_X,?_⟩
  · simp [weightedNorm]
  · exact (by simpa using parity_C 1 : Parity (1 : ℝ[X]) 0).congr (by norm_num)

/-- Completion degrees can be padded without changing the represented polynomial. -/
theorem HasCompletion.pad {A : ℝ[X]} {j k : ℕ} (hA : HasCompletion A j) (hjk : j ≤ k) :
    HasCompletion A k := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hjk
  induction m with
  | zero => simpa using hA
  | succ m ih => simpa [Nat.add_assoc] using (ih (by omega)).mul completion_one_odd

/-- Contracting an even polynomial and substituting X² recovers it exactly. -/
theorem expand_contract_even (A : ℝ[X]) (hA : Parity A 0) :
    expand ℝ 2 (contract 2 A) = A := by
  ext n
  rw [coeff_expand (by norm_num : 0 < 2), coeff_contract (by norm_num : (2 : ℕ) ≠ 0)]
  by_cases hd : 2 ∣ n
  · rw [if_pos hd, Nat.div_mul_cancel hd]
  · rw [if_neg hd]
    symm
    apply hA n
    intro hm
    apply hd
    exact Nat.dvd_of_mod_eq_zero (by simpa using hm)

/-- GSLW Lemma 6: a genuine weighted sum-of-squares completion with the
specified degrees and parities, proved by factor construction and induction. -/
theorem lemma6_real_completion (A : ℝ[X]) (k : ℕ)
    (hpar : Parity A 0) (hdegree : A.natDegree ≤ 2*k)
    (hA : ∀ x : ℝ, |x| ≤ 1 → 0 ≤ A.eval x) :
    ∃ B C : ℝ[X], A = weightedNorm B C ∧ B.natDegree ≤ k ∧
      (C = 0 ∨ C.natDegree < k) ∧ Parity B k ∧ Parity C (k+1) := by
  let D := contract 2 A
  have hexp : expand ℝ 2 D = A := expand_contract_even A hpar
  have hD : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ D.eval y := by
    intro y hy
    have hx : |Real.sqrt y| ≤ 1 := by
      rw [abs_of_nonneg (Real.sqrt_nonneg y)]
      exact (Real.sqrt_le_left (by norm_num)).mpr (by simpa using hy.2)
    have hh := hA (Real.sqrt y) hx
    rw [← hexp, expand_eq_comp_X_pow, eval_comp, eval_pow, eval_X, Real.sq_sqrt hy.1] at hh
    exact hh
  have hd : D.natDegree ≤ k := by
    have hh := congrArg Polynomial.natDegree hexp
    rw [natDegree_expand] at hh
    omega
  obtain ⟨B,C,hcomp,hB,hC,hBp,hCp⟩ := (interval_completion D hD).pad hd
  exact ⟨B,C,hexp.symm.trans hcomp,hB,hC,hBp,hCp⟩


end OptimalQLS.PolynomialTransform.Completion
