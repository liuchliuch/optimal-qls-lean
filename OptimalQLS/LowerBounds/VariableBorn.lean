import OptimalQLS.LowerBounds.VariableQueryPolynomial
import OptimalQLS.LowerBounds.PureDensity

/-! Born-mass conservation for literal rectangular finite instruments. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace OptimalQLS.LowerBounds
open Matrix

variable {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

theorem pureDensity_mulVec (G : Matrix E D ℂ) (v : D → ℂ) :
    pureDensity (G *ᵥ v) = G * pureDensity v * G.conjTranspose := by
  simp only [pureDensity, ketBra, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  congr 1
  ext j
  simp [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, mul_comm]

def bornMass (v : D → ℂ) : ℝ := ∑ i, Complex.normSq (v i)

theorem bornMass_eq_trace (v : D → ℂ) : bornMass v = (pureDensity v).trace.re := by
  simp [bornMass, pureDensity, ketBra, Matrix.trace_vecMulVec, dotProduct, Complex.mul_conj]

theorem bornMass_eq_norm_sq (v : D → ℂ) : bornMass v = ‖WithLp.toLp 2 v‖ ^ 2 := by
  rw [bornMass_eq_trace, pureDensity_trace, Complex.ofReal_re]

theorem rectangular_bornMass_eq_gram_trace (G : Matrix E D ℂ) (v : D → ℂ) :
    bornMass (G *ᵥ v) = ((G.conjTranspose * G) * pureDensity v).trace.re := by
  rw [bornMass_eq_trace, pureDensity_mulVec, Matrix.trace_mul_cycle]

theorem unitary_bornMass (U : Matrix.unitaryGroup D ℂ) (v : D → ℂ) :
    bornMass ((U : Matrix D D ℂ) *ᵥ v) = bornMass v := by
  have hU : (U : Matrix D D ℂ).conjTranspose * (U : Matrix D D ℂ) = 1 := U.property.1
  rw [rectangular_bornMass_eq_gram_trace, hU, Matrix.one_mul, bornMass_eq_trace]

/-- Different measurement outcomes may produce different finite workspace
sizes. Completeness is checked on the common input register. -/
theorem varying_instrument_bornMass {I : Type*} [Fintype I] (d : I → ℕ)
    (K : ∀ i, Matrix (Fin (d i)) D ℂ) (hK : ∑ i, (K i).conjTranspose * K i = 1) (v : D → ℂ) :
    (∑ i, bornMass (K i *ᵥ v)) = bornMass v := by
  simp only [rectangular_bornMass_eq_gram_trace]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul, hK, Matrix.one_mul, bornMass_eq_trace]

end OptimalQLS.LowerBounds
