import OptimalQLS.PolynomialTransform.PhaseCircuit
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Polynomial algebra underlying quantum signal phase factorization

This file develops the actual forward and backward polynomial recurrences
from GSLW Theorem 3. No phase-existence conclusion is postulated.
-/
noncomputable section
namespace OptimalQLS.PolynomialTransform.QSP
open Polynomial
open scoped ComplexConjugate

/-- Coefficientwise conjugation; the indeterminate is fixed. -/
def conjugate (P : ℂ[X]) : ℂ[X] := P.map (starRingEnd ℂ)

@[simp] theorem conjugate_coeff (P : ℂ[X]) (n : ℕ) :
    (conjugate P).coeff n = star (P.coeff n) := by simp [conjugate]
@[simp] theorem conjugate_zero : conjugate 0 = 0 := by simp [conjugate]
@[simp] theorem conjugate_one : conjugate 1 = 1 := by simp [conjugate]
@[simp] theorem conjugate_X : conjugate X = X := by simp [conjugate]
@[simp] theorem conjugate_C (z : ℂ) : conjugate (C z) = C (star z) := by simp [conjugate]
@[simp] theorem conjugate_add (P Q : ℂ[X]) : conjugate (P + Q) = conjugate P + conjugate Q := by
  simp [conjugate]
@[simp] theorem conjugate_sub (P Q : ℂ[X]) : conjugate (P - Q) = conjugate P - conjugate Q := by
  simp [conjugate]
@[simp] theorem conjugate_mul (P Q : ℂ[X]) : conjugate (P * Q) = conjugate P * conjugate Q := by
  simp [conjugate]
@[simp] theorem conjugate_pow (P : ℂ[X]) (n : ℕ) : conjugate (P ^ n) = conjugate P ^ n := by
  simp [conjugate]
@[simp] theorem conjugate_conjugate (P : ℂ[X]) : conjugate (conjugate P) = P := by
  ext n
  simp
@[simp] theorem conjugate_natDegree (P : ℂ[X]) : (conjugate P).natDegree = P.natDegree := by
  exact Polynomial.natDegree_map_eq_of_injective (star_injective) P
@[simp] theorem conjugate_eq_zero (P : ℂ[X]) : conjugate P = 0 ↔ P = 0 := by
  constructor
  · intro h
    have := congrArg conjugate h
    simpa using this
  · rintro rfl
    simp

/-- Constant polynomial with the actual unit-circle phase. -/
def phase (z : Circle) : ℂ[X] := C (z : ℂ)

@[simp] theorem conjugate_phase (z : Circle) : conjugate (phase z) = phase z⁻¹ := by
  simp only [phase, conjugate_C]
  congr 1
  exact (Circle.coe_inv_eq_conj z).symm

@[simp] theorem phase_mul_inverse (z : Circle) : phase z * phase z⁻¹ = 1 := by
  rw [phase, phase, ← map_mul]
  simp

/-- The polynomial normalization identity expressing pointwise unitarity. -/
def normPolynomial (P Q : ℂ[X]) : ℂ[X] :=
  P * conjugate P + (1 - X ^ 2) * Q * conjugate Q

/-- The exact forward recurrence on the two entries. -/
def forwardP (z : Circle) (P Q : ℂ[X]) : ℂ[X] :=
  phase z * (X * P + (X ^ 2 - 1) * Q)
def forwardQ (z : Circle) (P Q : ℂ[X]) : ℂ[X] :=
  phase z⁻¹ * (X * Q + P)

/-- The exact inverse recurrence used to remove the final signal step. -/
def lowerP (z : Circle) (P Q : ℂ[X]) : ℂ[X] :=
  phase z⁻¹ * X * P + phase z * (1 - X ^ 2) * Q
def lowerQ (z : Circle) (P Q : ℂ[X]) : ℂ[X] :=
  phase z * X * Q - phase z⁻¹ * P

/-- A removal step can be reconstructed without approximation. -/
theorem forward_lowerP (z : Circle) (P Q : ℂ[X]) :
    forwardP z (lowerP z P Q) (lowerQ z P Q) = P := by
  calc
    _ = (phase z * phase z⁻¹) * P := by unfold forwardP lowerP lowerQ; ring
    _ = P := by rw [phase_mul_inverse, one_mul]

theorem forward_lowerQ (z : Circle) (P Q : ℂ[X]) :
    forwardQ z (lowerP z P Q) (lowerQ z P Q) = Q := by
  calc
    _ = (phase z * phase z⁻¹) * Q := by unfold forwardQ lowerP lowerQ; ring
    _ = Q := by rw [phase_mul_inverse, one_mul]

/-- Both recurrences preserve the normalization polynomial exactly. -/
theorem normPolynomial_lower (z : Circle) (P Q : ℂ[X]) :
    normPolynomial (lowerP z P Q) (lowerQ z P Q) = normPolynomial P Q := by
  simp only [normPolynomial, lowerP, lowerQ, conjugate_add, conjugate_sub, conjugate_mul,
    conjugate_phase, conjugate_one, conjugate_X, conjugate_pow, inv_inv]
  calc
    _ = (phase z * phase z⁻¹) *
        (P * conjugate P + (1 - X ^ 2) * Q * conjugate Q) := by ring
    _ = _ := by rw [phase_mul_inverse, one_mul]

theorem normPolynomial_forward (z : Circle) (P Q : ℂ[X]) :
    normPolynomial (forwardP z P Q) (forwardQ z P Q) = normPolynomial P Q := by
  simp only [normPolynomial, forwardP, forwardQ, conjugate_add, conjugate_sub, conjugate_mul,
    conjugate_phase, conjugate_one, conjugate_X, conjugate_pow, inv_inv]
  calc
    _ = (phase z * phase z⁻¹) *
        (P * conjugate P + (1 - X ^ 2) * Q * conjugate Q) := by ring
    _ = _ := by rw [phase_mul_inverse, one_mul]

/-- Nonzero normalized pairs have adjacent degrees, derived from the
polynomial identity instead of added to a synthesis certificate. -/
theorem normalized_degree_relation {P Q : ℂ[X]}
    (hN : normPolynomial P Q = 1) (hQ : Q ≠ 0) :
    P ≠ 0 ∧ P.natDegree = Q.natDegree + 1 := by
  have hcQ : conjugate Q ≠ 0 := by simpa using hQ
  have hfactor : (X ^ 2 - 1 : ℂ[X]) ≠ 0 := by
    intro hz
    have hh := congrArg (fun p : ℂ[X] => p.coeff 2) hz
    norm_num [Polynomial.coeff_one] at hh
  have hd : ((X ^ 2 - 1) * Q * conjugate Q).natDegree = 2 + 2 * Q.natDegree := by
    rw [natDegree_mul (mul_ne_zero hfactor hQ) hcQ, natDegree_mul hfactor hQ,
      conjugate_natDegree]
    have hf : (X ^ 2 - 1 : ℂ[X]).natDegree = 2 := by
      simpa using (natDegree_X_pow_sub_C (R := ℂ) (n := 2) (r := 1))
    rw [hf]
    omega
  have hid : P * conjugate P = 1 + (X ^ 2 - 1) * Q * conjugate Q := by
    unfold normPolynomial at hN
    linear_combination hN
  have hright : (1 + (X ^ 2 - 1) * Q * conjugate Q).natDegree = 2 + 2 * Q.natDegree := by
    rw [natDegree_add_eq_right_of_natDegree_lt, hd]
    rw [natDegree_one, hd]
    omega
  have hP : P ≠ 0 := by
    intro hz
    have hh := congrArg Polynomial.natDegree hid
    rw [hz, zero_mul, natDegree_zero, hright] at hh
    omega
  refine ⟨hP, ?_⟩
  have hcP : conjugate P ≠ 0 := by simpa using hP
  have hh := congrArg Polynomial.natDegree hid
  rw [natDegree_mul hP hcP, conjugate_natDegree, hright] at hh
  omega

@[simp] theorem conjugate_leadingCoeff (P : ℂ[X]) :
    (conjugate P).leadingCoeff = star P.leadingCoeff := by
  simp only [Polynomial.leadingCoeff, conjugate_natDegree, conjugate_coeff]

/-- The normalization identity forces equal magnitudes of the leading entries. -/
theorem normalized_leading_relation {P Q : ℂ[X]}
    (hN : normPolynomial P Q = 1) (hQ : Q ≠ 0) :
    P.leadingCoeff * star P.leadingCoeff = Q.leadingCoeff * star Q.leadingCoeff := by
  have hcQ : conjugate Q ≠ 0 := by simpa using hQ
  have hfdeg : (X ^ 2 - 1 : ℂ[X]).natDegree = 2 := by
    simpa using (natDegree_X_pow_sub_C (R := ℂ) (n := 2) (r := 1))
  have hf : (X ^ 2 - 1 : ℂ[X]) ≠ 0 := by
    intro hz
    simp [hz] at hfdeg
  have hp : (X ^ 2 - 1) * Q * conjugate Q ≠ 0 := mul_ne_zero (mul_ne_zero hf hQ) hcQ
  have hd : (1 : ℂ[X]).degree < ((X ^ 2 - 1) * Q * conjugate Q).degree := by
    rw [degree_one, degree_eq_natDegree hp]
    have hh : 0 < ((X ^ 2 - 1) * Q * conjugate Q).natDegree := by
      rw [natDegree_mul (mul_ne_zero hf hQ) hcQ, natDegree_mul hf hQ, hfdeg]
      omega
    exact_mod_cast hh
  have hid : P * conjugate P = 1 + (X ^ 2 - 1) * Q * conjugate Q := by
    unfold normPolynomial at hN
    linear_combination hN
  have hh := congrArg Polynomial.leadingCoeff hid
  simpa only [leadingCoeff_mul, conjugate_leadingCoeff,
    leadingCoeff_add_of_degree_lt hd, leadingCoeff_X_pow_sub_one (by norm_num : 0 < 2),
    one_mul] using hh

/-- An actual unit-circle phase cancelling the leading terms is derived
from normalization and algebraic closure of the complex numbers. -/
theorem exists_leading_phase {P Q : ℂ[X]} (hN : normPolynomial P Q = 1) (hQ : Q ≠ 0) :
    ∃ z : Circle, ((z⁻¹ : Circle) : ℂ) * P.leadingCoeff = (z : ℂ) * Q.leadingCoeff := by
  have hq : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ
  have hm := normalized_leading_relation hN hQ
  have hn : ‖P.leadingCoeff‖ = ‖Q.leadingCoeff‖ := by
    simp only [RCLike.star_def, Complex.mul_conj] at hm
    have hn' := Complex.ofReal_injective hm
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hn'
    nlinarith [norm_nonneg P.leadingCoeff, norm_nonneg Q.leadingCoeff]
  have hr : ‖P.leadingCoeff / Q.leadingCoeff‖ = 1 := by
    rw [norm_div, hn, div_self (norm_ne_zero_iff.mpr hq)]
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (P.leadingCoeff / Q.leadingCoeff)
    (by norm_num : 0 < 2)
  have hwn : ‖w‖ = 1 := by
    have hh := congrArg norm hw
    rw [norm_pow, hr] at hh
    nlinarith [norm_nonneg w]
  let z : Circle := ⟨w, by simpa [Submonoid.unitSphere, Metric.mem_sphere, dist_zero_right] using hwn⟩
  refine ⟨z, ?_⟩
  change w⁻¹ * P.leadingCoeff = w * Q.leadingCoeff
  have hwne : w ≠ 0 := norm_ne_zero_iff.mp (by rw [hwn]; norm_num)
  have hh : w ^ 2 * Q.leadingCoeff = P.leadingCoeff := by rw [hw]; field_simp
  rw [← hh]
  field_simp

/-- Coefficient-support parity, including the zero polynomial. -/
def HasParity (P : ℂ[X]) (k : ℕ) : Prop :=
  ∀ n, n % 2 ≠ k % 2 → P.coeff n = 0

theorem HasParity.congr {P : ℂ[X]} {j k : ℕ} (hP : HasParity P j)
    (hjk : j % 2 = k % 2) : HasParity P k := by
  intro n hn
  exact hP n (by simpa [hjk] using hn)

theorem HasParity.add {P Q : ℂ[X]} {k : ℕ} (hP : HasParity P k) (hQ : HasParity Q k) :
    HasParity (P + Q) k := by
  intro n hn
  simp [coeff_add, hP n hn, hQ n hn]

theorem HasParity.sub {P Q : ℂ[X]} {k : ℕ} (hP : HasParity P k) (hQ : HasParity Q k) :
    HasParity (P - Q) k := by
  intro n hn
  simp [coeff_sub, hP n hn, hQ n hn]

theorem HasParity.C_mul {P : ℂ[X]} {k : ℕ} (hP : HasParity P k) (c : ℂ) :
    HasParity (C c * P) k := by
  intro n hn
  simp [coeff_C_mul, hP n hn]

theorem HasParity.X_mul {P : ℂ[X]} {k : ℕ} (hP : HasParity P k) :
    HasParity (X * P) (k + 1) := by
  intro n hn
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_X_mul]
    exact hP n (by omega)

theorem HasParity.X_sq_mul {P : ℂ[X]} {k : ℕ} (hP : HasParity P k) :
    HasParity (X ^ 2 * P) k := by
  have hh := hP.X_mul.X_mul
  rw [← mul_assoc, ← pow_two] at hh
  exact hh.congr (by omega)

theorem HasParity.natDegree {P : ℂ[X]} {k : ℕ} (hP : HasParity P k) (hp : P ≠ 0) :
    P.natDegree % 2 = k % 2 := by
  by_contra h
  exact (leadingCoeff_ne_zero.mpr hp) (hP P.natDegree h)

/-- Lowering reverses the two coefficient parities. -/
theorem lower_parities {P Q : ℂ[X]} {k : ℕ}
    (hP : HasParity P (k + 1)) (hQ : HasParity Q k) (z : Circle) :
    HasParity (lowerP z P Q) k ∧ HasParity (lowerQ z P Q) (k + 1) := by
  have hxP : HasParity (X * P) k := hP.X_mul.congr (by omega)
  have hQsub : HasParity ((1 - X ^ 2) * Q) k := by
    rw [sub_mul, one_mul]
    exact hQ.sub hQ.X_sq_mul
  constructor
  · unfold lowerP phase
    rw [mul_assoc, mul_assoc]
    exact (hxP.C_mul _).add (hQsub.C_mul _)
  · unfold lowerQ phase
    rw [mul_assoc]
    exact (hQ.X_mul.C_mul _).sub (hP.C_mul _)


/-- Every normalized pair has a nonzero primary entry. -/
theorem normalized_P_ne_zero {P Q : ℂ[X]} (hN : normPolynomial P Q = 1) : P ≠ 0 := by
  by_cases hQ : Q = 0
  · intro hP
    simp [normPolynomial, hP, hQ] at hN
  · exact (normalized_degree_relation hN hQ).1

/-- A vanishing secondary entry forces a constant primary polynomial. -/
theorem normalized_Q_zero_degree {P : ℂ[X]} (hN : normPolynomial P 0 = 1) : P.natDegree = 0 := by
  have hp := normalized_P_ne_zero hN
  have hc : conjugate P ≠ 0 := by simpa using hp
  have hh := congrArg Polynomial.natDegree hN
  simp only [normPolynomial, conjugate_zero, mul_zero, add_zero, natDegree_one] at hh
  rw [natDegree_mul hp hc, conjugate_natDegree] at hh
  omega

/-- The leading phase really cancels the highest secondary coefficient. -/
theorem lowerQ_degree_lt {P Q : ℂ[X]} (hN : normPolynomial P Q = 1) (hQ : Q ≠ 0)
    (z : Circle) (hz : ((z⁻¹ : Circle) : ℂ) * P.leadingCoeff = (z : ℂ) * Q.leadingCoeff) :
    (lowerQ z P Q).degree < P.degree := by
  obtain ⟨hP, hdegree⟩ := normalized_degree_relation hN hQ
  have hz0 : (z : ℂ) ≠ 0 := Circle.coe_ne_zero z
  have hzi0 : ((z⁻¹ : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero z⁻¹
  have hleft : C (z : ℂ) * X * Q ≠ 0 := mul_ne_zero
    (mul_ne_zero (C_ne_zero.mpr hz0) X_ne_zero) hQ
  have hright : C ((z⁻¹ : Circle) : ℂ) * P ≠ 0 := mul_ne_zero (C_ne_zero.mpr hzi0) hP
  have hdleft : (C (z : ℂ) * X * Q).degree = P.degree := by
    rw [degree_eq_natDegree hleft, degree_eq_natDegree hP]
    congr 1
    rw [mul_assoc, natDegree_C_mul hz0, natDegree_mul X_ne_zero hQ, natDegree_X]
    omega
  have hdright : (C ((z⁻¹ : Circle) : ℂ) * P).degree = P.degree := by
    rw [degree_C_mul hzi0]
  have hlc : (C (z : ℂ) * X * Q).leadingCoeff =
      (C ((z⁻¹ : Circle) : ℂ) * P).leadingCoeff := by
    simpa only [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X, mul_one] using hz.symm
  unfold lowerQ phase
  rw [← hdleft]
  exact degree_sub_lt (hdleft.trans hdright.symm) hleft hlc

/-- The primary degree strictly decreases; parity rules out a surviving
coefficient of the original degree after leading-term cancellation. -/
theorem lowerP_natDegree_lt {P Q : ℂ[X]} (hN : normPolynomial P Q = 1) (hQ : Q ≠ 0)
    (hPpar : HasParity P (Q.natDegree + 1)) (hQpar : HasParity Q Q.natDegree)
    (z : Circle) (hz : ((z⁻¹ : Circle) : ℂ) * P.leadingCoeff = (z : ℂ) * Q.leadingCoeff) :
    (lowerP z P Q).natDegree < P.natDegree := by
  have hd := (normalized_degree_relation hN hQ).2
  have hNlo : normPolynomial (lowerP z P Q) (lowerQ z P Q) = 1 := by
    rw [normPolynomial_lower, hN]
  have hPlone := normalized_P_ne_zero hNlo
  by_cases hQlo : lowerQ z P Q = 0
  · rw [hQlo] at hNlo
    rw [normalized_Q_zero_degree hNlo, hd]
    omega
  · have hdlo := (normalized_degree_relation hNlo hQlo).2
    have hQlt : (lowerQ z P Q).natDegree < P.natDegree := by
      apply (natDegree_lt_iff_degree_lt hQlo).mpr
      rw [← degree_eq_natDegree (normalized_P_ne_zero hN)]
      exact lowerQ_degree_lt hN hQ z hz
    have hpmod := (lower_parities hPpar hQpar z).1.natDegree hPlone
    omega

/-- A strictly smaller normalized pair and a reconstructing phase are
obtained from any nonconstant normalized parity pair. -/
theorem exists_lowering {P Q : ℂ[X]} (hN : normPolynomial P Q = 1) (hQ : Q ≠ 0)
    (hPpar : HasParity P P.natDegree) (hQpar : HasParity Q (P.natDegree + 1)) :
    ∃ z : Circle,
      normPolynomial (lowerP z P Q) (lowerQ z P Q) = 1 ∧
      (lowerP z P Q).natDegree < P.natDegree ∧
      HasParity (lowerP z P Q) (lowerP z P Q).natDegree ∧
      HasParity (lowerQ z P Q) ((lowerP z P Q).natDegree + 1) := by
  obtain ⟨z, hz⟩ := exists_leading_phase hN hQ
  have hd := (normalized_degree_relation hN hQ).2
  have hp : HasParity P (Q.natDegree + 1) := by simpa [hd] using hPpar
  have hq : HasParity Q Q.natDegree := hQpar.congr (by omega)
  have hNlo : normPolynomial (lowerP z P Q) (lowerQ z P Q) = 1 := by
    rw [normPolynomial_lower, hN]
  have hpars := lower_parities hp hq z
  have hmod := hpars.1.natDegree (normalized_P_ne_zero hNlo)
  refine ⟨z, hNlo, lowerP_natDegree_lt hN hQ hp hq z hz, ?_, ?_⟩
  · exact hpars.1.congr hmod.symm
  · exact hpars.2.congr (by omega)

/-- Exact polynomials synthesized by a finite phase sequence. Phases are
stored with the outermost (last-applied recurrence) first. -/
def sequencePair (z₀ : Circle) : List Circle → ℂ[X] × ℂ[X]
  | [] => (phase z₀, 0)
  | z :: zs =>
    let pq := sequencePair z₀ zs
    (forwardP z pq.1 pq.2, forwardQ z pq.1 pq.2)

/-- The constant case has an actual unit-circle phase. -/
theorem normalized_constant_phase {P : ℂ[X]} (hN : normPolynomial P 0 = 1) :
    ∃ z : Circle, P = phase z := by
  have hd := normalized_Q_zero_degree hN
  have hP : P = C (P.coeff 0) := eq_C_of_natDegree_eq_zero hd
  have hn : ‖P.coeff 0‖ = 1 := by
    rw [hP] at hN
    have hh := congrArg (fun p : ℂ[X] => p.coeff 0) hN
    simp only [normPolynomial, conjugate_C, conjugate_zero, mul_zero, add_zero,
      ← map_mul, coeff_C_zero, coeff_one_zero] at hh
    rw [RCLike.star_def, Complex.mul_conj] at hh
    have he : Complex.normSq (P.coeff 0) = 1 := Complex.ofReal_injective (by simpa using hh)
    rw [Complex.normSq_eq_norm_sq] at he
    nlinarith [norm_nonneg (P.coeff 0)]
  exact ⟨⟨P.coeff 0, by simpa [Submonoid.unitSphere, Metric.mem_sphere, dist_zero_right] using hn⟩, hP⟩

/-- GSLW Theorem 3's algebraic synthesis direction: the complete normalized
polynomial pair is factored into a finite list of actual unit-circle phases.
The normalization and parity are mathematical hypotheses of that theorem,
not a QSVT circuit or phase-existence certificate. -/
theorem normalized_pair_factorization (P Q : ℂ[X])
    (hN : normPolynomial P Q = 1)
    (hPpar : HasParity P P.natDegree) (hQpar : HasParity Q (P.natDegree + 1)) :
    ∃ (z₀ : Circle) (zs : List Circle), sequencePair z₀ zs = (P, Q) ∧ zs.length ≤ P.natDegree := by
  generalize hn : P.natDegree = n
  induction n using Nat.strong_induction_on generalizing P Q with
  | h n ih =>
    by_cases hQ : Q = 0
    · rw [hQ] at hN ⊢
      obtain ⟨z₀, hz₀⟩ := normalized_constant_phase hN
      exact ⟨z₀, [], by simp [sequencePair, hz₀], Nat.zero_le _⟩
    · obtain ⟨z, hNlo, hlt, hp, hq⟩ := exists_lowering hN hQ hPpar hQpar
      obtain ⟨z₀, zs, hzs, hlen⟩ := ih (lowerP z P Q).natDegree (by omega)
        (lowerP z P Q) (lowerQ z P Q) hNlo hp hq rfl
      refine ⟨z₀, z :: zs, ?_, ?_⟩
      · simp only [sequencePair, hzs, forward_lowerP, forward_lowerQ]
      · simp only [List.length_cons]
        omega


end OptimalQLS.PolynomialTransform.QSP
