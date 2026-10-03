import OptimalQLS.OracleCircuit
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Tactic

/-! # The concrete fractional-linear transducer (Proposition 4.6) -/

noncomputable section
namespace OptimalQLS
open Matrix
open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

def fractionalDenominator (U : Matrix.unitaryGroup n ℂ) (r : ℝ) : Matrix n n ℂ :=
  1 - r • (U : Matrix n n ℂ)

def fractionalNumerator (U : Matrix.unitaryGroup n ℂ) (r : ℝ) : Matrix n n ℂ :=
  (U : Matrix n n ℂ) - r • (1 : Matrix n n ℂ)

theorem fractionalDenominator_isUnit (U : Matrix.unitaryGroup n ℂ) {r : ℝ}
    (hr : |r| < 1) : IsUnit (fractionalDenominator U r) := by
  cases isEmpty_or_nonempty n with
  | inl hn =>
    letI := hn
    have hD : fractionalDenominator U r = 1 := Subsingleton.elim _ _
    rw [hD]
    exact isUnit_one
  | inr hn =>
    letI := hn
    apply isUnit_one_sub_of_norm_lt_one
    rw [norm_smul, Real.norm_eq_abs, CStarRing.norm_coe_unitary, mul_one]
    exact hr

theorem fractional_gram_identity (U : Matrix.unitaryGroup n ℂ) (r : ℝ) :
    star (fractionalNumerator U r) * fractionalNumerator U r =
      star (fractionalDenominator U r) * fractionalDenominator U r := by
  have hU : star (U : Matrix n n ℂ) * (U : Matrix n n ℂ) = 1 := U.property.1
  simp only [fractionalNumerator, fractionalDenominator, star_sub, star_smul,
    star_trivial, star_one, sub_mul, mul_sub, one_mul, mul_one,
    smul_mul_assoc, mul_smul_comm, hU]
  module

def fractionalAction (U : Matrix.unitaryGroup n ℂ) (r : ℝ) : Matrix n n ℂ :=
  fractionalNumerator U r * Ring.inverse (fractionalDenominator U r)

theorem fractionalAction_unitary (U : Matrix.unitaryGroup n ℂ) {r : ℝ}
    (hr : |r| < 1) : fractionalAction U r ∈ Matrix.unitaryGroup n ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  have hD := fractionalDenominator_isUnit U hr
  rw [fractionalAction, Matrix.star_mul]
  calc
    star (Ring.inverse (fractionalDenominator U r)) * star (fractionalNumerator U r) *
        (fractionalNumerator U r * Ring.inverse (fractionalDenominator U r)) =
      star (Ring.inverse (fractionalDenominator U r)) *
        (star (fractionalNumerator U r) * fractionalNumerator U r) *
        Ring.inverse (fractionalDenominator U r) := by simp [mul_assoc]
    _ = star (Ring.inverse (fractionalDenominator U r)) *
        (star (fractionalDenominator U r) * fractionalDenominator U r) *
        Ring.inverse (fractionalDenominator U r) := by rw [fractional_gram_identity]
    _ = 1 := by
      rw [mul_assoc, mul_assoc, Ring.mul_inverse_cancel _ hD, mul_one,
        ← Matrix.star_mul, Ring.mul_inverse_cancel _ hD, star_one]

/-- Real two-label mixing matrix, with one public and one private copy. -/
def fractionalMix (r : ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  let t := Real.sqrt (1 - r ^ 2)
  Matrix.fromBlocks ((-r) • (1 : Matrix n n ℂ)) (t • 1) (t • 1) (r • 1)

omit [Fintype n] in
theorem fractionalMix_selfAdjoint (r : ℝ) : star (fractionalMix (n := n) r) = fractionalMix r := by
  simp [fractionalMix, Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose]

theorem fractionalMix_square {r : ℝ} (hr : |r| < 1) :
    fractionalMix (n := n) r * fractionalMix r = 1 := by
  have hr2 : 0 ≤ 1 - r ^ 2 := by nlinarith [(abs_lt.mp hr).1, (abs_lt.mp hr).2]
  have ht : Real.sqrt (1 - r ^ 2) * Real.sqrt (1 - r ^ 2) = 1 - r ^ 2 :=
    Real.mul_self_sqrt hr2
  have h1 : (-r) * (-r) + Real.sqrt (1 - r ^ 2) * Real.sqrt (1 - r ^ 2) = 1 := by nlinarith [ht]
  have h2 : (-r) * Real.sqrt (1 - r ^ 2) + Real.sqrt (1 - r ^ 2) * r = 0 := by ring
  have h3 : Real.sqrt (1 - r ^ 2) * (-r) + r * Real.sqrt (1 - r ^ 2) = 0 := by ring
  have h4 : Real.sqrt (1 - r ^ 2) * Real.sqrt (1 - r ^ 2) + r * r = 1 := by nlinarith [ht]
  unfold fractionalMix
  rw [Matrix.fromBlocks_multiply]
  simp only [mul_smul_comm, mul_one, smul_smul, ← add_smul]
  rw [h1, h2, h3, h4]
  simp only [one_smul, zero_smul, Matrix.fromBlocks_one]

theorem fractionalMix_unitary {r : ℝ} (hr : |r| < 1) :
    fractionalMix (n := n) r ∈ Matrix.unitaryGroup (n ⊕ n) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  rw [fractionalMix_selfAdjoint, fractionalMix_square hr]

def fractionalCatalyst (U : Matrix.unitaryGroup n ℂ) (r : ℝ) (ξ : n → ℂ) : n → ℂ :=
  Real.sqrt (1 - r ^ 2) • (Ring.inverse (fractionalDenominator U r) *ᵥ ξ)

/-- The exact identity restoring the catalyst, proved from the concrete
inverse and actual block matrix. -/
theorem fractional_transduction (U : Matrix.unitaryGroup n ℂ) {r : ℝ}
    (hr : |r| < 1) (ξ : n → ℂ) :
    fractionalMix r *ᵥ (Sum.elim ξ ((U : Matrix n n ℂ) *ᵥ fractionalCatalyst U r ξ)) =
      Sum.elim (fractionalAction U r *ᵥ ξ) (fractionalCatalyst U r ξ) := by
  let v := Ring.inverse (fractionalDenominator U r) *ᵥ ξ
  let t := Real.sqrt (1 - r ^ 2)
  have hr2 : 0 ≤ 1 - r ^ 2 := by nlinarith [(abs_lt.mp hr).1, (abs_lt.mp hr).2]
  have ht : t * t = 1 - r * r := by
    simpa [t, pow_two] using Real.mul_self_sqrt hr2
  have hv : ξ = v - r • ((U : Matrix n n ℂ) *ᵥ v) := by
    have h := congrArg (fun M : Matrix n n ℂ => M *ᵥ ξ)
      (Ring.mul_inverse_cancel (fractionalDenominator U r) (fractionalDenominator_isUnit U hr))
    simpa only [← Matrix.mulVec_mulVec, fractionalDenominator, Matrix.sub_mulVec,
      Matrix.one_mulVec, Matrix.smul_mulVec] using h.symm
  have hact : fractionalAction U r *ᵥ ξ = (U : Matrix n n ℂ) *ᵥ v - r • v := by
    unfold fractionalAction
    rw [← Matrix.mulVec_mulVec]
    simp only [fractionalNumerator, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  have hfirst : (-r) • ξ + t • ((U : Matrix n n ℂ) *ᵥ (t • v)) =
      (U : Matrix n n ℂ) *ᵥ v - r • v := by
    rw [hv, Matrix.mulVec_smul, smul_smul, ht]
    module
  have hsecond : t • ξ + r • ((U : Matrix n n ℂ) *ᵥ (t • v)) = t • v := by
    rw [hv, Matrix.mulVec_smul]
    module
  unfold fractionalMix
  rw [Matrix.fromBlocks_mulVec]
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec]
  change Sum.elim ((-r) • ξ + t • ((U : Matrix n n ℂ) *ᵥ (t • v)))
    (t • ξ + r • ((U : Matrix n n ℂ) *ᵥ (t • v))) = _
  rw [hfirst, hsecond, ← hact]
  rfl


/-- One oracle call on the private label, identity on the public label. -/
def privateOracle (U : Matrix.unitaryGroup n ℂ) : Matrix.unitaryGroup (n ⊕ n) ℂ :=
  ⟨Matrix.fromBlocks 1 0 0 (U : Matrix n n ℂ), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    have hU : (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 := U.property.2
    simpa [hU] using (Matrix.fromBlocks_one :
      Matrix.fromBlocks (1 : Matrix n n ℂ) 0 0 1 = 1)⟩

/-- The actual canonical transducer B_r (I ⊕ U). -/
def fractionalTransducer (U : Matrix.unitaryGroup n ℂ) (r : ℝ) (hr : |r| < 1) :
    Matrix.unitaryGroup (n ⊕ n) ℂ :=
  ⟨fractionalMix r, fractionalMix_unitary hr⟩ * privateOracle U

/-- **Proposition 4.6**, as one concrete finite-matrix endpoint. -/
theorem proposition46 (U : Matrix.unitaryGroup n ℂ) (r : ℝ) (hr : |r| < 1) :
    IsUnit (fractionalDenominator U r) ∧
    fractionalAction U r ∈ Matrix.unitaryGroup n ℂ ∧
    ∀ ξ : n → ℂ,
      (fractionalTransducer U r hr : Matrix (n ⊕ n) (n ⊕ n) ℂ) *ᵥ
        Sum.elim ξ (fractionalCatalyst U r ξ) =
      Sum.elim (fractionalAction U r *ᵥ ξ) (fractionalCatalyst U r ξ) := by
  refine ⟨fractionalDenominator_isUnit U hr, fractionalAction_unitary U hr, ?_⟩
  intro ξ
  change (fractionalMix r * Matrix.fromBlocks 1 0 0 (U : Matrix n n ℂ)) *ᵥ _ = _
  rw [← Matrix.mulVec_mulVec, Matrix.fromBlocks_mulVec]
  simpa using fractional_transduction U hr ξ

end OptimalQLS
