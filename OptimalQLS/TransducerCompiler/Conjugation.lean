import OptimalQLS.TransducerCompiler.Basic

noncomputable section
namespace OptimalQLS.TransducerCompiler
open Matrix

private theorem isometric_action_conjugation {G E : Type*} [Group G]
    [NormedAddCommGroup E] (f : G → E → E)
    (hmul : ∀ a b x, f (a*b) x = f a (f b x))
    (hsub : ∀ a x y, f a (x-y) = f a x - f a y)
    (hnorm : ∀ a x, ‖f a x‖ = ‖x‖) (p u : G) (x y : E) :
    ‖f (p⁻¹*u*p) x - y‖ = ‖f u (f p x) - f p y‖ := by
  have hc : p * (p⁻¹ * u * p) = u * p := by
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  calc
    _ = ‖f p (f (p⁻¹*u*p) x - y)‖ := (hnorm p _).symm
    _ = ‖f p (f (p⁻¹*u*p) x) - f p y‖ := by rw [hsub]
    _ = ‖f (p*(p⁻¹*u*p)) x - f p y‖ :=
      congrArg (fun z => ‖z - f p y‖) (hmul p (p⁻¹*u*p) x).symm
    _ = ‖f u (f p x) - f p y‖ := by rw [hc, hmul]

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- General conjugation preserves an implementation error. -/
theorem conjugation_error (P U : Matrix.unitaryGroup n ℂ) (x y : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (P⁻¹ * U * P).val x - y‖ =
      ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) U.val
        (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) P.val x) -
        Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) P.val y‖ := by
  apply isometric_action_conjugation
    (fun (a : Matrix.unitaryGroup n ℂ) v =>
      Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) a.val v)
  · intro a b v
    change Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (a.val * b.val) v = _
    rw [map_mul]
    rfl
  · intro a v w
    exact map_sub _ _ _
  · intro a v
    exact unitary_norm a v

end OptimalQLS.TransducerCompiler
