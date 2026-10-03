import OptimalQLS.Geometry.NormBounds
import Mathlib.Algebra.Ring.Units

noncomputable section
namespace OptimalQLS.Geometry
variable {ι : Type*} [Fintype ι]

/-- Loewner comparison expressed through complex quadratic forms.
This definition uses the actual Hilbert inner product. -/
def QuadraticLE (S T : Vec ι →L[ℂ] Vec ι) : Prop :=
  ∀ x, (inner ℂ x (S x)).re ≤ (inner ℂ x (T x)).re

/-- The quadratic form of a real diagonal operator. -/
theorem diagonal_real_quadratic (f : ι → ℝ) (x : Vec ι) :
    (inner ℂ x (diagonal (fun i => (f i : ℂ)) x)).re =
      ∑ i, f i * ‖x i‖ ^ 2 := by
  simp only [PiLp.inner_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [RCLike.inner_apply, Complex.mul_re, Complex.mul_im, Complex.sq_norm,
    Complex.normSq_apply]
  <;> ring

/-- Real diagonal matrices are Hermitian. -/
theorem diagonal_real_symmetric (f : ι → ℝ) :
    (diagonal (fun i => (f i : ℂ))).toLinearMap.IsSymmetric := by
  intro x y
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [RCLike.inner_apply, map_mul]
  <;> ring

/-- The correction matrix lies between I and 2I in Loewner order. -/
theorem correction_operator_bounds (a : ι → ℝ) {t : ℝ} (ht : 0 < t)
    (ha : ∀ i, t ≤ |a i|) :
    QuadraticLE 1 (diagonal (fun i => ((1 + t ^ 2 / a i ^ 2 : ℝ) : ℂ))) ∧
    QuadraticLE (diagonal (fun i => ((1 + t ^ 2 / a i ^ 2 : ℝ) : ℂ))) (2 • (1 : Vec ι →L[ℂ] Vec ι)) := by
  have h₁ : (1 : Vec ι →L[ℂ] Vec ι) = diagonal (fun _ => (1 : ℂ)) := by
    ext; simp
  have h₂ : 2 • (1 : Vec ι →L[ℂ] Vec ι) = diagonal (fun _ => ((2 : ℝ) : ℂ)) := by
    ext; simp
  rw [h₂, h₁]
  constructor
  · intro x
    have hq := diagonal_real_quadratic (fun _ : ι => (1 : ℝ)) x
    simp only [Complex.ofReal_one] at hq
    change (inner ℂ x (diagonal (fun _ => (1 : ℂ)) x)).re ≤ _
    rw [hq, diagonal_real_quadratic]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (correction_coefficient_bounds ht (ha i)).1 (sq_nonneg _)
  · intro x
    change (inner ℂ x (diagonal (fun i => ((1 + t ^ 2 / a i ^ 2 : ℝ) : ℂ)) x)).re ≤ _
    rw [diagonal_real_quadratic, diagonal_real_quadratic]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (correction_coefficient_bounds ht (ha i)).2 (sq_nonneg _)

/-- Exact Proposition 5.3 correction identity for concrete diagonal operators. -/
theorem correction_operator_identity (a : ι → ℝ) {t : ℝ} (ht : 0 < t)
    (ha : ∀ i, a i ≠ 0) :
    diagonal (fun i => ((1 + t ^ 2 / a i ^ 2 : ℝ) : ℂ)) *
      diagonal (fun i => (a i : ℂ)) *
      diagonal (fun i => (((a i ^ 2 + t ^ 2)⁻¹ : ℝ) : ℂ)) =
    diagonal (fun i => (((a i)⁻¹ : ℝ) : ℂ)) := by
  ext x i
  simp only [ContinuousLinearMap.mul_apply, diagonal_apply]
  have h := correction_coefficient_identity (ha i) ht
  have hc : ((1 + t ^ 2 / a i ^ 2 : ℝ) : ℂ) *
      ((a i : ℂ) / ((a i : ℂ)^2 + (t : ℂ)^2)) = ((a i : ℂ)⁻¹) := by
    exact_mod_cast h
  push_cast
  push_cast at hc
  simp only [div_eq_mul_inv] at hc
  calc
    _ = (((1 : ℂ) + (t : ℂ)^2 / (a i : ℂ)^2) *
      ((a i : ℂ) * ((a i : ℂ)^2 + (t : ℂ)^2)⁻¹)) * x i := by ring
    _ = _ := by simpa only [div_eq_mul_inv] using congrArg (fun z : ℂ => z * x i) hc

/-- The correction factor has exactly the algebraic form I+t²A⁻². -/
theorem correction_operator_formula (a : ι → ℝ) (t : ℝ) :
    diagonal (fun i => ((1 + t ^ 2 / a i ^ 2 : ℝ) : ℂ)) =
      1 + (t ^ 2 : ℂ) • (diagonal (fun i => ((a i)⁻¹ : ℂ))) ^ 2 := by
  ext x i
  simp [pow_two, ContinuousLinearMap.mul_apply, div_eq_mul_inv]
  <;> ring

end OptimalQLS.Geometry
