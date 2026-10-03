import OptimalQLS.TransducerCompiler.Error
import OptimalQLS.TransducerCompiler.ClockUnitary

noncomputable section
namespace OptimalQLS.TransducerCompiler
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {K : ℕ}

/-- Public input with a clean computational-basis clock. -/
def inputState (zero : Fin K) (ξ : n → ℂ) : Space n K → ℂ
  | ((i,.pub),k) => if k = zero then ξ i else 0
  | ((_,.internal),_) => 0
  | ((_,.first),_) => 0
  | ((_,.second),_) => 0

theorem prepare_input (zero : Fin K) (ξ : n → ℂ) :
    ((clockLift (n := n) (clockPrepare zero) : Matrix (Space n K) (Space n K) ℂ) *ᵥ
      inputState zero ξ) =
      (((Real.sqrt (K : ℝ))⁻¹ : ℝ) : ℂ) • publicState ξ := by
  ext ⟨⟨i,l⟩,k⟩
  rw [clockLift_apply]
  cases l with
  | pub =>
    have hcol : (clockPrepare zero).val k zero = (((Real.sqrt (K : ℝ))⁻¹ : ℝ) : ℂ) := by
      have h := congrFun (clockPrepare_mulVec_single zero) k
      simpa only [Matrix.mulVec_single, MulOpposite.op_one, one_smul,
        Matrix.col_apply, Complex.ofReal_inv] using h
    have hv : (fun j => inputState zero ξ ((i,Label.pub),j)) = Pi.single zero (ξ i) := by
      ext j
      simp [inputState, Pi.single_apply]
    rw [hv, Matrix.mulVec_single]
    change (clockPrepare zero).val k zero * ξ i = _
    rw [hcol]
    simp [publicState, mul_comm]
  | internal => simp [inputState, publicState, Matrix.mulVec, dotProduct]
  | first => simp [inputState, publicState, Matrix.mulVec, dotProduct]
  | second => simp [inputState, publicState, Matrix.mulVec, dotProduct]


end OptimalQLS.TransducerCompiler
