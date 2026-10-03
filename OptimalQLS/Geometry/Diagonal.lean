import OptimalQLS.Geometry.ScalarBounds
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic.FinCases

/-!
# Auxiliary geometry in an orthonormal spectral coordinate system

`Vec` and `Triple` carry the actual complex Euclidean L2 norm, not the
coordinatewise sup norm. `auxiliary`, `kernelProjector`, and `pseudoInverse`
are concrete complex continuous linear maps. The real coordinates `a i`
are the eigenvalues of the input Hermitian operator; transport from an
arbitrary Hermitian operator is handled separately.
-/
noncomputable section
open scoped ComplexConjugate
namespace OptimalQLS.Geometry

abbrev Vec (ι : Type*) := EuclideanSpace ℂ ι
abbrev Triple (ι : Type*) := EuclideanSpace ℂ (Fin 3 × ι)
variable {ι : Type*} [Fintype ι]

def triple (x y z : Vec ι) : Triple ι :=
  WithLp.toLp 2 (fun ji => ![x ji.2, y ji.2, z ji.2] ji.1)

@[simp] theorem triple_zero (x y z : Vec ι) (i : ι) : triple x y z (0,i) = x i := rfl
@[simp] theorem triple_one (x y z : Vec ι) (i : ι) : triple x y z (1,i) = y i := rfl
@[simp] theorem triple_two (x y z : Vec ι) (i : ι) : triple x y z (2,i) = z i := rfl

def diagonal (f : ι → ℂ) : Vec ι →L[ℂ] Vec ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i => f i * x i)
      map_add' := by intros; ext; simp [mul_add]
      map_smul' := by intros; ext; simp [mul_comm, mul_left_comm] }

@[simp] theorem diagonal_apply (f : ι → ℂ) (x : Vec ι) (i : ι) :
    diagonal f x i = f i * x i := rfl

def auxiliary (a : ι → ℝ) (t : ℝ) : Triple ι →L[ℂ] Triple ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 fun ji =>
        ![(a ji.2 : ℂ) * x (1,ji.2) - t * x (2,ji.2),
          (a ji.2 : ℂ) * x (0,ji.2), -(t : ℂ) * x (0,ji.2)] ji.1
      map_add' := by
        intros; ext ⟨j,i⟩; fin_cases j <;> simp <;> ring
      map_smul' := by
        intros; ext ⟨j,i⟩; fin_cases j <;> simp <;> ring }

@[simp] theorem auxiliary_zero (a : ι → ℝ) (t : ℝ) (x : Triple ι) (i : ι) :
    auxiliary a t x (0,i) = (a i : ℂ) * x (1,i) - t * x (2,i) := rfl
@[simp] theorem auxiliary_one (a : ι → ℝ) (t : ℝ) (x : Triple ι) (i : ι) :
    auxiliary a t x (1,i) = (a i : ℂ) * x (0,i) := rfl
@[simp] theorem auxiliary_two (a : ι → ℝ) (t : ℝ) (x : Triple ι) (i : ι) :
    auxiliary a t x (2,i) = -(t : ℂ) * x (0,i) := rfl

def kernelProjector (a : ι → ℝ) (t : ℝ) : Triple ι →L[ℂ] Triple ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 fun ji =>
        ![0, ((t : ℂ)^2 * x (1,ji.2) + t * (a ji.2) * x (2,ji.2)) /
               ((a ji.2 : ℂ)^2 + (t : ℂ)^2),
          (t * (a ji.2 : ℂ) * x (1,ji.2) + (a ji.2 : ℂ)^2 * x (2,ji.2)) /
               ((a ji.2 : ℂ)^2 + (t : ℂ)^2)] ji.1
      map_add' := by
        intros; ext ⟨j,i⟩; fin_cases j <;> simp <;> ring
      map_smul' := by
        intros; ext ⟨j,i⟩; fin_cases j <;> simp <;> ring }

def pseudoInverse (a : ι → ℝ) (t : ℝ) : Triple ι →L[ℂ] Triple ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 fun ji =>
        ![((a ji.2 : ℂ) * x (1,ji.2) - t * x (2,ji.2)) /
               ((a ji.2 : ℂ)^2 + (t : ℂ)^2),
          (a ji.2 : ℂ) * x (0,ji.2) / ((a ji.2 : ℂ)^2 + (t : ℂ)^2),
          -(t : ℂ) * x (0,ji.2) / ((a ji.2 : ℂ)^2 + (t : ℂ)^2)] ji.1
      map_add' := by
        intros; ext ⟨j,i⟩; fin_cases j <;> simp <;> ring
      map_smul' := by
        intros; ext ⟨j,i⟩; fin_cases j <;> simp <;> ring }

private theorem complex_denominator_ne_zero (a : ℝ) {t : ℝ} (ht : 0 < t) :
    (a : ℂ)^2 + (t : ℂ)^2 ≠ 0 := by
  exact_mod_cast ne_of_gt (denominator_pos (a := a) ht)

/-- The explicitly displayed kernel component belongs to the actual kernel. -/
theorem auxiliary_mul_projector (a : ι → ℝ) (t : ℝ) :
    auxiliary a t * kernelProjector a t = 0 := by
  ext x ⟨j,i⟩
  fin_cases j <;> simp [kernelProjector, auxiliary, ContinuousLinearMap.mul_apply] <;> ring <;> simp

/-- The first Moore–Penrose decomposition identity. -/
theorem auxiliary_mul_pseudoInverse (a : ι → ℝ) {t : ℝ} (ht : 0 < t) :
    auxiliary a t * pseudoInverse a t = 1 - kernelProjector a t := by
  ext x ⟨j,i⟩
  have hd := complex_denominator_ne_zero (a i) ht
  fin_cases j <;>
    simp [kernelProjector, auxiliary, pseudoInverse, ContinuousLinearMap.mul_apply] <;>
    field_simp <;> ring

/-- The second Moore–Penrose decomposition identity. -/
theorem pseudoInverse_mul_auxiliary (a : ι → ℝ) {t : ℝ} (ht : 0 < t) :
    pseudoInverse a t * auxiliary a t = 1 - kernelProjector a t := by
  ext x ⟨j,i⟩
  have hd := complex_denominator_ne_zero (a i) ht
  fin_cases j <;>
    simp [kernelProjector, auxiliary, pseudoInverse, ContinuousLinearMap.mul_apply] <;>
    field_simp <;> ring

/-- The pseudoinverse kills the kernel component. -/
theorem pseudoInverse_mul_projector (a : ι → ℝ) (t : ℝ) :
    pseudoInverse a t * kernelProjector a t = 0 := by
  ext x ⟨j,i⟩
  fin_cases j <;>
    simp [kernelProjector, pseudoInverse, ContinuousLinearMap.mul_apply] <;> ring <;> simp

/-- Exact kernel projection formula in Lemma 4.2. -/
theorem kernelProjector_input (a : ι → ℝ) (t : ℝ) (b : Vec ι) :
    kernelProjector a t (triple 0 b 0) =
      triple 0 (diagonal (fun i => (t : ℂ)^2 / ((a i : ℂ)^2 + (t : ℂ)^2)) b)
        (diagonal (fun i => t * (a i : ℂ) / ((a i : ℂ)^2 + (t : ℂ)^2)) b) := by
  ext ⟨j,i⟩
  fin_cases j <;> simp [kernelProjector, triple] <;> ring

/-- Exact pseudoinverse formula in Lemma 4.2. -/
theorem pseudoInverse_input (a : ι → ℝ) (t : ℝ) (b : Vec ι) :
    pseudoInverse a t (triple 0 b 0) =
      triple (diagonal (fun i => (a i : ℂ) / ((a i : ℂ)^2 + (t : ℂ)^2)) b) 0 0 := by
  ext ⟨j,i⟩
  fin_cases j <;> simp [pseudoInverse, triple] <;> ring

/-- The auxiliary block matrix is Hermitian. -/
theorem auxiliary_symmetric (a : ι → ℝ) (t : ℝ) :
    (auxiliary a t).toLinearMap.IsSymmetric := by
  intro x y
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, Fin.sum_univ_three]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp [RCLike.inner_apply, auxiliary, map_sub, map_mul]
  <;> ring

/-- The displayed projector is precisely mathlib's orthogonal projection
onto the kernel, rather than merely an idempotent with an assigned name. -/
theorem kernelProjector_eq_orthogonalProjection (a : ι → ℝ) {t : ℝ} (ht : 0 < t) :
    kernelProjector a t = (LinearMap.ker (auxiliary a t).toLinearMap).starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · change auxiliary a t (kernelProjector a t x) = 0
    have h := congrArg (fun T : Triple ι →L[ℂ] Triple ι => T x)
      (auxiliary_mul_projector a t)
    simpa using h
  · intro w hw
    have hdecomp : x - kernelProjector a t x = auxiliary a t (pseudoInverse a t x) := by
      have h := congrArg (fun T : Triple ι →L[ℂ] Triple ι => T x)
        (auxiliary_mul_pseudoInverse a ht)
      simpa using h.symm
    rw [hdecomp]
    change auxiliary a t w = 0 at hw
    calc
      inner ℂ (auxiliary a t (pseudoInverse a t x)) w =
          inner ℂ (pseudoInverse a t x) (auxiliary a t w) := auxiliary_symmetric a t _ _
      _ = 0 := by simp [hw]

/-- Moore–Penrose reflexive identities, established for the actual operator. -/
theorem moore_penrose_reflexive (a : ι → ℝ) {t : ℝ} (ht : 0 < t) :
    auxiliary a t * pseudoInverse a t * auxiliary a t = auxiliary a t ∧
      pseudoInverse a t * auxiliary a t * pseudoInverse a t = pseudoInverse a t := by
  constructor
  · rw [mul_assoc, pseudoInverse_mul_auxiliary a ht, mul_sub, mul_one,
      auxiliary_mul_projector, sub_zero]
  · rw [mul_assoc, auxiliary_mul_pseudoInverse a ht, mul_sub, mul_one,
      pseudoInverse_mul_projector, sub_zero]

/-- A normalized kernel projection is killed by the pseudoinverse. -/
theorem pseudoInverse_normalized_projection (a : ι → ℝ) (t : ℝ) (x : Triple ι) :
    pseudoInverse a t ((‖kernelProjector a t x‖⁻¹ : ℂ) • kernelProjector a t x) = 0 := by
  rw [map_smul]
  have h := congrArg (fun T : Triple ι →L[ℂ] Triple ι => T x)
    (pseudoInverse_mul_projector a t)
  have h' : pseudoInverse a t (kernelProjector a t x) = 0 := by simpa using h
  simp [h']

end OptimalQLS.Geometry
