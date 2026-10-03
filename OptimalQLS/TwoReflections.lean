import OptimalQLS.MatrixPseudoInverse
import OptimalQLS.TwoReflectionScalars
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

noncomputable section
namespace OptimalQLS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Literal reflection about a Hermitian projection, as a verified unitary. -/
def projectionReflectionUnitary (P : E →L[ℂ] E) (hP : IsSelfAdjoint P)
    (hPP : P * P = P) : unitary (E →L[ℂ] E) :=
  ⟨(2 : ℝ) • P - 1, by
    have hs : star ((2 : ℝ) • P - 1) = (2 : ℝ) • P - 1 := by
      change star P = P at hP
      simp [star_smul, hP]
    have hh : ((2 : ℝ) • P - 1) * ((2 : ℝ) • P - 1) = 1 := by
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hPP, mul_one, one_mul]
      module
    constructor <;> rw [hs] <;> exact hh⟩

def vectorReflectionUnitary (e : E) (he : ‖e‖ = 1) : unitary (E →L[ℂ] E) :=
  projectionReflectionUnitary (InnerProductSpace.rankOne ℂ e e)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (InnerProductSpace.isSymmetric_rankOne_self e))
    (InnerProductSpace.isIdempotentElem_rankOne_self he)

/-- The actual signed product of the two reflections in Lemma4.7. -/
def twoReflectionUnitary (P : E →L[ℂ] E) (hP : IsSelfAdjoint P) (hPP : P * P = P)
    (e : E) (he : ‖e‖ = 1) : unitary (E →L[ℂ] E) :=
  -(vectorReflectionUnitary e he * projectionReflectionUnitary P hP hPP)

@[simp] theorem vectorReflectionUnitary_apply (e : E) (he : ‖e‖ = 1) (v : E) :
    (vectorReflectionUnitary e he : E →L[ℂ] E) v = (2 * inner ℂ e v) • e - v := by
  simp [vectorReflectionUnitary, projectionReflectionUnitary, smul_smul,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]

/-- Exact real-plane matrix in the nonnormalized orthogonal basis Pe,(I-P)e. -/
theorem twoReflection_plane (P : E →L[ℂ] E) (hP : IsSelfAdjoint P) (hPP : P * P = P)
    (e : E) (he : ‖e‖ = 1) (p w : E) (hepw : e = p + w)
    (hPp : P p = p) (hPw : P w = 0) {x : ℝ}
    (hep : inner ℂ e p = (x : ℂ)) (hew : inner ℂ e w = (1 - x : ℝ)) :
    (twoReflectionUnitary P hP hPP e he : E →L[ℂ] E) p =
      (1 - 2*x) • p - (2*x) • w ∧
    (twoReflectionUnitary P hP hPP e he : E →L[ℂ] E) w =
      (2*(1-x)) • p + (1 - 2*x) • w := by
  have hRp : (projectionReflectionUnitary P hP hPP : E →L[ℂ] E) p = p := by
    simp [projectionReflectionUnitary, hPp, two_smul]
  have hRw : (projectionReflectionUnitary P hP hPP : E →L[ℂ] E) w = -w := by
    simp [projectionReflectionUnitary, hPw]
  constructor
  · change -((vectorReflectionUnitary e he : E →L[ℂ] E)
      ((projectionReflectionUnitary P hP hPP : E →L[ℂ] E) p)) = _
    rw [hRp, vectorReflectionUnitary_apply, hep, hepw]
    have hc (y : ℝ) : (2 : ℂ) * (y : ℂ) = ((2*y : ℝ) : ℂ) := by push_cast; rfl
    rw [hc]
    have hr (a : ℝ) (v : E) : ((a : ℂ) • v) = a • v := by
      exact (RCLike.real_smul_eq_coe_smul (K := ℂ) a v).symm
    rw [hr]
    module
  · change -((vectorReflectionUnitary e he : E →L[ℂ] E)
      ((projectionReflectionUnitary P hP hPP : E →L[ℂ] E) w)) = _
    rw [hRw, map_neg, neg_neg, vectorReflectionUnitary_apply, hew, hepw]
    have hc (y : ℝ) : (2 : ℂ) * (y : ℂ) = ((2*y : ℝ) : ℂ) := by push_cast; rfl
    rw [hc]
    have hr (a : ℝ) (v : E) : ((a : ℂ) • v) = a • v := by
      exact (RCLike.real_smul_eq_coe_smul (K := ℂ) a v).symm
    rw [hr]
    module

end OptimalQLS
