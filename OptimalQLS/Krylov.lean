import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Real Krylov invariants for exact kernel alignment

These are concrete linear-algebra lemmas used in the proof of paper Lemma 4.9.
They do not claim that the finite preparation compiler has been implemented.
-/

noncomputable section
namespace OptimalQLS

section RealModule
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Real, algebraic Krylov span, including the zeroth power. -/
def realKrylov (H : Module.End ℝ E) (e : E) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range fun n : ℕ => (H ^ n) e)

theorem pow_apply_mem_realKrylov (H : Module.End ℝ E) (e : E) (n : ℕ) :
    (H ^ n) e ∈ realKrylov H e :=
  Submodule.subset_span ⟨n, rfl⟩

theorem self_mem_realKrylov (H : Module.End ℝ E) (e : E) :
    e ∈ realKrylov H e := by
  simpa using pow_apply_mem_realKrylov H e 0

theorem map_mem_realKrylov (H : Module.End ℝ E) (e : E) {v : E}
    (hv : v ∈ realKrylov H e) : H v ∈ realKrylov H e := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    simpa only [pow_succ', Module.End.mul_apply] using
      pow_apply_mem_realKrylov H e (n + 1)
  | zero => simp [map_zero]
  | add x y _ _ hx hy => simpa using (realKrylov H e).add_mem hx hy
  | smul a x _ hx => simpa using (realKrylov H e).smul_mem a hx

theorem annihilates_positive_power (P H : Module.End ℝ E)
    (hPH : P * H = 0) (e : E) (n : ℕ) :
    P ((H ^ (n + 1)) e) = 0 := by
  have hh : P * H ^ (n + 1) = 0 := by
    rw [pow_succ', ← mul_assoc, hPH, zero_mul]
  exact congrArg (fun T : Module.End ℝ E => T e) hh

/-- The exact direction statement: a real Krylov vector projects to a real
multiple of the projected initial vector. It only uses the exact relation PH=0. -/
theorem projection_realKrylov_collinear (P H : Module.End ℝ E)
    (hPH : P * H = 0) (e : E) {v : E} (hv : v ∈ realKrylov H e) :
    ∃ c : ℝ, P v = c • P e := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    cases n with
    | zero => exact ⟨1, by simp⟩
    | succ n => exact ⟨0, by simpa using annihilates_positive_power P H hPH e n⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp [ha, hb, add_smul]⟩
  | smul a x _ hx =>
    obtain ⟨b, hb⟩ := hx
    exact ⟨a * b, by simp [hb, mul_smul]⟩

end RealModule

section ComplexHilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
open scoped ComplexInnerProductSpace

/-- The Krylov span of a complex operator is taken over real coefficients. -/
def hermitianKrylov (H : E →L[ℂ] E) (e : E) : Submodule ℝ E :=
  realKrylov (H.toLinearMap.restrictScalars ℝ) e

omit [CompleteSpace E] in
theorem restrictScalars_pow_apply (H : E →L[ℂ] E) (n : ℕ) (e : E) :
    ((H.toLinearMap.restrictScalars ℝ) ^ n) e = (H ^ n) e := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', Module.End.mul_apply, ContinuousLinearMap.mul_apply]
    exact congrArg H ih

/-- Real moments are a consequence of Hermiticity, not an input assumption. -/
theorem inner_im_eq_zero_of_mem_hermitianKrylov (H : E →L[ℂ] E)
    (hH : IsSelfAdjoint H) (e : E) {v : E} (hv : v ∈ hermitianKrylov H e) :
    Complex.im ⟪e, v⟫ = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    change Complex.im ⟪e, ((H.toLinearMap.restrictScalars ℝ) ^ n) e⟫ = 0
    rw [restrictScalars_pow_apply]
    exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hH.pow n)).im_inner_self_apply e
  | zero => simp
  | add x y _ _ hx hy => simp [inner_add_right, hx, hy]
  | smul a x _ hx =>
    rw [inner_smul_right_eq_smul]
    simp [hx]

/-- Reflection about a unit vector, as an actual vector operation. -/
def inputReflection (e v : E) : E := (2 * ⟪e, v⟫) • e - v

theorem inputReflection_mem_hermitianKrylov (H : E →L[ℂ] E)
    (hH : IsSelfAdjoint H) (e : E) {v : E} (hv : v ∈ hermitianKrylov H e) :
    inputReflection e v ∈ hermitianKrylov H e := by
  have him := inner_im_eq_zero_of_mem_hermitianKrylov H hH e hv
  have he : e ∈ hermitianKrylov H e :=
    self_mem_realKrylov (H.toLinearMap.restrictScalars ℝ) e
  have hc : (2 * ⟪e, v⟫) = ((2 * Complex.re ⟪e, v⟫ : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  unfold inputReflection
  rw [hc]
  exact (hermitianKrylov H e).sub_mem
    (by simpa only [Complex.coe_smul] using (hermitianKrylov H e).smul_mem (2 * Complex.re ⟪e, v⟫) he) hv

end ComplexHilbert
end OptimalQLS
