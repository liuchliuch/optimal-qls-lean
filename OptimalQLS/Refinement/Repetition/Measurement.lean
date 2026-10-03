import OptimalQLS.LowerBounds.FiniteProgramTruncation
import OptimalQLS.LowerBounds.FiniteProgramDensity

/-! A literal coordinate-success instrument.  Success preserves all amplitudes
in the designated output subspace. Failure measures the rejected basis label
and prepares the fixed initial basis state, so every retry uses the same quantum
register, rather than allocating a tensor product of copies. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.Refinement.Repetition
open Matrix LowerBounds
set_option maxHeartbeats 500000
variable {d w : ℕ}

def basis (a : Fin w) : Fin w → ℂ := fun i => if i = a then 1 else 0

def acceptMatrix (e : Fin d ↪ Fin w) : Matrix (Fin d) (Fin w) ℂ :=
  fun i j => if e i = j then 1 else 0

def rejectAmplitude (e : Fin d ↪ Fin w) (v : Fin w → ℂ) (j : Fin w) : ℂ :=
  if ∃ i, e i = j then 0 else v j

def resetMatrix (e : Fin d ↪ Fin w) (zero j : Fin w) : Matrix (Fin w) (Fin w) ℂ :=
  if ∃ i, e i = j then 0 else abortBasisKraus zero j

theorem acceptMatrix_mulVec (e : Fin d ↪ Fin w) (v : Fin w → ℂ) :
    acceptMatrix e *ᵥ v = fun i => v (e i) := by
  ext i
  simp [acceptMatrix, Matrix.mulVec, dotProduct]

theorem resetMatrix_mulVec (e : Fin d ↪ Fin w) (zero j : Fin w) (v : Fin w → ℂ) :
    resetMatrix e zero j *ᵥ v = rejectAmplitude e v j • basis zero := by
  by_cases h : ∃ i, e i = j
  · simp [resetMatrix, rejectAmplitude, h]
  · ext i
    simp [resetMatrix, rejectAmplitude, h, abortBasisKraus, Matrix.mulVec, dotProduct, basis]

theorem basis_bornMass (a : Fin w) : bornMass (basis a) = 1 := by
  simp [bornMass, basis, apply_ite]

theorem basis_norm (a : Fin w) : ‖WithLp.toLp 2 (basis a)‖ = 1 := by
  have h := basis_bornMass a
  rw [bornMass_eq_norm_sq] at h
  nlinarith [norm_nonneg (WithLp.toLp 2 (basis a))]

theorem resetMatrix_gram (e : Fin d ↪ Fin w) (zero j i k : Fin w) :
    ((resetMatrix e zero j).conjTranspose * resetMatrix e zero j) i k =
      if ∃ x, e x = j then 0 else if i = j ∧ k = j then 1 else 0 := by
  by_cases h : ∃ x, e x = j
  · simp [resetMatrix, h]
  · simp [resetMatrix, h, abortBasisKraus, Matrix.mul_apply, Matrix.conjTranspose_apply]
    split_ifs <;> simp_all

theorem coordinate_instrument_complete (e : Fin d ↪ Fin w) (zero : Fin w) :
    (acceptMatrix e).conjTranspose * acceptMatrix e +
      ∑ j, (resetMatrix e zero j).conjTranspose * resetMatrix e zero j = 1 := by
  classical
  ext i j
  simp only [Matrix.add_apply, Matrix.sum_apply, resetMatrix_gram]
  by_cases hij : i = j
  · subst j
    by_cases h : ∃ k, e k = i
    · obtain ⟨k, rfl⟩ := h
      have he (x : Fin d) : e x = e k ↔ x = k := e.injective.eq_iff
      have hz (x : Fin w) : (if ∃ a, e a = x then (0 : ℂ) else if e k = x then 1 else 0) = 0 := by
        split_ifs with h₁ h₂
        · rfl
        · exact False.elim (h₁ ⟨k, h₂⟩)
        · rfl
      simp [acceptMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, he, hz]
    · have hne (k : Fin d) : e k ≠ i := fun hk => h ⟨k, hk⟩
      have hz (x : Fin w) : (if ∃ a, e a = x then (0 : ℂ) else if i = x then 1 else 0) =
          if i = x then 1 else 0 := by
        by_cases hx : i = x
        · subst x; simp [h]
        · simp [hx]
      simp [acceptMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, hne, hz]
  · have hzero (k : Fin d) : (if e k = i then (1 : ℂ) else 0) *
        (if e k = j then (1 : ℂ) else 0) = 0 := by
      split_ifs with hi hj <;> simp_all
    have hz (x : Fin w) : ¬ (i = x ∧ j = x) := by
      rintro ⟨rfl, rfl⟩; exact hij rfl
    simp [acceptMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, hzero, hz, hij]

def nextDimension (d w : ℕ) : Fin (w + 1) → ℕ := Fin.cases d (fun _ => w)

def measurementKraus (e : Fin d ↪ Fin w) (zero : Fin w) :
    (i : Fin (w + 1)) → Matrix (Fin (nextDimension d w i)) (Fin w) ℂ :=
  Fin.cases (acceptMatrix e) (fun j => resetMatrix e zero j)

theorem measurementKraus_complete (e : Fin d ↪ Fin w) (zero : Fin w) :
    (∑ i, (measurementKraus e zero i).conjTranspose * measurementKraus e zero i) = 1 := by
  rw [Fin.sum_univ_succ]
  exact coordinate_instrument_complete e zero

theorem bornMass_smul (a : ℂ) (v : Fin w → ℂ) :
    bornMass (a • v) = Complex.normSq a * bornMass v := by
  simp [bornMass, Complex.normSq_mul, Finset.mul_sum]

theorem pureDensity_complex_smul (a : ℂ) (v : Fin w → ℂ) :
    pureDensity (a • v) = Complex.normSq a • pureDensity v := by
  ext i j
  simp [pureDensity, ketBra, Matrix.vecMulVec, Complex.normSq_eq_conj_mul_self,
    Complex.real_smul, mul_comm, mul_left_comm, mul_assoc]

theorem rejection_mass (e : Fin d ↪ Fin w) (zero : Fin w) (v : Fin w → ℂ) :
    (∑ j, Complex.normSq (rejectAmplitude e v j)) =
      bornMass v - bornMass (fun i => v (e i)) := by
  have h := varying_instrument_bornMass (nextDimension d w)
    (measurementKraus e zero) (measurementKraus_complete e zero) v
  rw [Fin.sum_univ_succ] at h
  change bornMass (acceptMatrix e *ᵥ v) +
    (∑ j, bornMass (resetMatrix e zero j *ᵥ v)) = bornMass v at h
  simp only [acceptMatrix_mulVec, resetMatrix_mulVec, bornMass_smul, basis_bornMass, mul_one] at h
  linarith

end OptimalQLS.Refinement.Repetition
