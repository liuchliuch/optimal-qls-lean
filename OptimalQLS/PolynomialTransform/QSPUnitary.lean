import OptimalQLS.PolynomialTransform.QSPFactorization

/-! # Exact two-dimensional unitary semantics of the factored QSP polynomials -/
noncomputable section
namespace OptimalQLS.PolynomialTransform.QSP
open Polynomial Matrix
open scoped ComplexConjugate

/-- The signal rotation W(x), with its actual square-root off-diagonal. -/
def scalarSignalMatrix (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(x : ℂ), Complex.I * Real.sqrt (1 - x^2);
    Complex.I * Real.sqrt (1 - x^2), (x : ℂ)]

theorem signal_sqrt_identity {x : ℝ} (hx : |x| ≤ 1) :
    (x : ℂ)^2 + (Real.sqrt (1 - x^2) : ℂ)^2 = 1 := by
  have hx2 : x^2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
  have hs := Real.sq_sqrt (sub_nonneg.mpr hx2)
  exact_mod_cast (show x^2 + (Real.sqrt (1-x^2))^2 = 1 by linarith)

/-- W(x) is a verified, concrete 2-by-2 unitary for every promised signal. -/
def scalarSignalUnitary (x : ℝ) (hx : |x| ≤ 1) : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨scalarSignalMatrix x, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    have hs := signal_sqrt_identity hx
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, scalarSignalMatrix,
        Matrix.conjTranspose_apply, Matrix.one_apply, Complex.conj_ofReal,
        Complex.conj_I] <;> ring_nf <;> simp [Complex.I_sq] <;>
      first | linear_combination hs | ring⟩

/-- The actual diagonal phase gate diag(z, z^-1). -/
def scalarPhaseGate (z : Circle) : Matrix.unitaryGroup (Fin 2) ℂ :=
  diagonalPhase ![z, z⁻¹]

@[simp] theorem scalarPhaseGate_entries (z : Circle) :
    (scalarPhaseGate z : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(z : ℂ), 0; 0, ((z⁻¹ : Circle) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalarPhaseGate, diagonalPhase]

/-- The matrix encoded by a pair of QSP polynomials. -/
def pairMatrix (P Q : ℂ[X]) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![P.eval (x : ℂ), Complex.I * Q.eval (x : ℂ) * Real.sqrt (1-x^2);
    Complex.I * star (Q.eval (x : ℂ)) * Real.sqrt (1-x^2), star (P.eval (x : ℂ))]

/-- The polynomial recurrence is exactly multiplication by W(x) and the
actual diagonal phase. This is an equality of every matrix entry. -/
theorem pairMatrix_forward (z : Circle) (P Q : ℂ[X]) {x : ℝ} (hx : |x| ≤ 1) :
    pairMatrix (forwardP z P Q) (forwardQ z P Q) x =
      pairMatrix P Q x * scalarSignalMatrix x * (scalarPhaseGate z : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hs : (Real.sqrt (1-x^2) : ℂ)^2 = 1 - (x : ℂ)^2 := by
    linear_combination signal_sqrt_identity hx
  have hz : star (z : ℂ) = ((z⁻¹ : Circle) : ℂ) := (Circle.coe_inv_eq_conj z).symm
  have hzi : star ((z⁻¹ : Circle) : ℂ) = (z : ℂ) := by
    simpa using (Circle.coe_inv_eq_conj z⁻¹).symm
  rw [scalarPhaseGate_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, pairMatrix, scalarSignalMatrix,
      forwardP, forwardQ, phase, hz, hzi] <;>
    ring_nf <;> simp [Complex.I_sq, hs] <;> ring

@[simp] theorem pairMatrix_initial (z : Circle) (x : ℝ) :
    pairMatrix (phase z) 0 x = (scalarPhaseGate z : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [scalarPhaseGate_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairMatrix, phase, ← Circle.coe_inv_eq_conj]

/-- A finite product of actual 2-by-2 unitary matrices. -/
def scalarSequence (x : ℝ) (hx : |x| ≤ 1) (z₀ : Circle) :
    List Circle → Matrix.unitaryGroup (Fin 2) ℂ
  | [] => scalarPhaseGate z₀
  | z :: zs => scalarSequence x hx z₀ zs * scalarSignalUnitary x hx * scalarPhaseGate z

/-- Every synthesized polynomial pair is realized by its actual phase product. -/
theorem scalarSequence_eq_pairMatrix (x : ℝ) (hx : |x| ≤ 1) (z₀ : Circle)
    (zs : List Circle) :
    (scalarSequence x hx z₀ zs : Matrix (Fin 2) (Fin 2) ℂ) =
      pairMatrix (sequencePair z₀ zs).1 (sequencePair z₀ zs).2 x := by
  induction zs with
  | nil => exact (pairMatrix_initial z₀ x).symm
  | cons z zs ih =>
    simp only [scalarSequence, sequencePair]
    rw [pairMatrix_forward z _ _ hx]
    change ((scalarSequence x hx z₀ zs : Matrix (Fin 2) (Fin 2) ℂ) * scalarSignalMatrix x) *
      (scalarPhaseGate z : Matrix (Fin 2) (Fin 2) ℂ) = _
    rw [ih]

/-- The normalized-pair direction of GSLW Theorem 3, including actual
unitary realization and the degree-bound on the number of signal uses. -/
theorem normalized_pair_unitary_realization (P Q : ℂ[X])
    (hN : normPolynomial P Q = 1)
    (hPpar : HasParity P P.natDegree) (hQpar : HasParity Q (P.natDegree + 1)) :
    ∃ (z₀ : Circle) (zs : List Circle), zs.length ≤ P.natDegree ∧
      ∀ (x : ℝ) (hx : |x| ≤ 1),
        (scalarSequence x hx z₀ zs : Matrix (Fin 2) (Fin 2) ℂ) = pairMatrix P Q x := by
  obtain ⟨z₀, zs, hpq, hlen⟩ := normalized_pair_factorization P Q hN hPpar hQpar
  refine ⟨z₀, zs, hlen, ?_⟩
  intro x hx
  rw [scalarSequence_eq_pairMatrix, hpq]

end OptimalQLS.PolynomialTransform.QSP
