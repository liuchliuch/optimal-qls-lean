import OptimalQLS.PhysicalRobustness.SpectralCutoff
import OptimalQLS.PhysicalPadding.Operators

/-! Spectral separation of an arbitrary Hermitian perturbation of a
zero-padded, invertible logical operator. -/
noncomputable section
namespace OptimalQLS.PhysicalRobustness
open Geometry PhysicalPadding Matrix
open scoped Matrix.Norms.L2Operator

section Abstract
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- A real diagonal operator bounded away from zero expands every vector. -/
theorem diagonal_norm_lower {ι : Type*} [Fintype ι] (a : ι → ℝ)
    {r : ℝ} (hr : 0 ≤ r) (ha : ∀ i, r ≤ |a i|) (x : Vec ι) :
    r*‖x‖ ≤ ‖diagonal (fun i => (a i : ℂ)) x‖ := by
  apply (sq_le_sq₀ (mul_nonneg hr (norm_nonneg _)) (norm_nonneg _)).mp
  rw [mul_pow, diagonal_real_norm_sq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  simpa only [sq_abs] using (sq_le_sq₀ hr (abs_nonneg _)).mpr (ha i)

/-- The noisy spectrum lies within `δ` of zero or beyond `g-δ`, where `g`
is the original nonzero gap.  The proof uses an eigenvector residual and
Parseval, and does not posit spectral perturbation as an oracle fact. -/
theorem noisy_spectral_gap
    (H B : E →L[ℂ] E) (hH : H.toLinearMap.IsSymmetric) (hB : B.toLinearMap.IsSymmetric)
    {g δ : ℝ} (hδ : 0 ≤ δ)
    (hgap : ∀ i, hH.eigenvalues rfl i = 0 ∨ g ≤ |hH.eigenvalues rfl i|)
    (hpert : ‖B-H‖ ≤ δ) (j : Fin (Module.finrank ℂ E)) :
    |hB.eigenvalues rfl j| ≤ δ ∨ g-δ ≤ |hB.eigenvalues rfl j| := by
  by_contra hn
  push_neg at hn
  let lam := hB.eigenvalues rfl j
  let v := hB.eigenvectorBasis rfl j
  let U := (hH.eigenvectorBasis rfl).repr
  let r := min |lam| (g-|lam|)
  have hr : δ < r := lt_min hn.1 (by dsimp [lam]; linarith [hn.2])
  have hv : ‖v‖ = 1 := (hB.eigenvectorBasis rfl).orthonormal.norm_eq_one j
  have he : B v = (lam : ℂ) • v :=
    Module.End.mem_eigenspace_iff.mp (hB.hasEigenvector_eigenvectorBasis rfl j).1
  have hcoord : U ((H-B) v) =
      diagonal (fun i => ((hH.eigenvalues rfl i-lam : ℝ) : ℂ)) (U v) := by
    ext i
    simp only [ContinuousLinearMap.sub_apply, map_sub, he, map_smul, PiLp.sub_apply,
      PiLp.smul_apply, smul_eq_mul, Geometry.diagonal_apply]
    change U (H v) i-(lam : ℂ)*U v i = _
    have hd : U (H v) i = (hH.eigenvalues rfl i : ℂ)*U v i :=
      hH.eigenvectorBasis_apply_self_apply rfl v i
    rw [hd]
    push_cast
    ring
  have hlower : r*‖U v‖ ≤ ‖U ((H-B) v)‖ := by
    rw [hcoord]
    apply diagonal_norm_lower _ (hδ.trans hr.le)
    intro i
    rcases hgap i with hz | hi
    · rw [hz, zero_sub, abs_neg]
      exact min_le_left |lam| (g-|lam|)
    · have htri : |hH.eigenvalues rfl i|-|lam| ≤ |hH.eigenvalues rfl i-lam| :=
        abs_sub_abs_le_abs_sub _ _
      exact (min_le_right |lam| (g-|lam|)).trans (by linarith)
  rw [U.norm_map, U.norm_map, hv, mul_one] at hlower
  have hupper : ‖(H-B) v‖ ≤ δ := by
    have hp : ‖H-B‖ ≤ δ := by simpa only [norm_sub_rev] using hpert
    exact ((H-B).le_opNorm v).trans (by simpa [hv] using hp)
  linarith
end Abstract

section Physical
variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

/-- Nonzero padded eigenvalues are genuine logical eigenvalues.  Restriction
is nonzero because the full zero extension annihilates all unused columns. -/
theorem zeroExtend_nonzero_eigenvalue_gap (f : D ↪ P) (A : Matrix D D ℂ)
    (hA : IsUnit A) {κ : ℝ} (hκ : 0 < κ) (hinv : ‖Ring.inverse A‖ ≤ κ)
    {μ : ℂ} (hμ : μ ≠ 0) (v : EuclideanSpace ℂ P) (hv : v ≠ 0)
    (he : Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) (zeroExtend f A) v = μ • v) :
    κ⁻¹ ≤ ‖μ‖ := by
  let R := restriction f
  let T := Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ) A
  have hr : T (R v) = μ • R v := by
    rw [← zeroExtend_restrict f A v, he, map_smul]
  have hRne : R v ≠ 0 := by
    intro hz
    have hzero : Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) (zeroExtend f A) v = 0 := by
      change WithLp.toLp 2 ((insertion f*A*(insertion f)ᴴ)*ᵥWithLp.ofLp v) = 0
      rw [← Matrix.mulVec_mulVec]
      have hrz : (insertion f)ᴴ*ᵥWithLp.ofLp v = 0 := by
        ext i
        simpa only [insertion_adjoint_mulVec] using congrArg (fun x : EuclideanSpace ℂ D => x i) hz
      rw [hrz, Matrix.mulVec_zero]
      rfl
    rw [he] at hzero
    exact hv ((smul_eq_zero.mp hzero).resolve_left hμ)
  have hT : IsUnit T := hA.map (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)).toMonoidHom
  have hi : ‖Ring.inverse T‖ ≤ κ := by
    rw [← Perturbation.toEuclideanCLM_inverse A hA]
    exact hinv
  have hc : Ring.inverse T (T (R v)) = R v := by
    exact congrArg (fun L : EuclideanSpace ℂ D →L[ℂ] EuclideanSpace ℂ D => L (R v))
      (Ring.inverse_mul_cancel T hT)
  have hn : ‖R v‖ ≤ κ*‖μ‖*‖R v‖ := by
    calc
      ‖R v‖ = ‖Ring.inverse T (T (R v))‖ := by rw [hc]
      _ ≤ ‖Ring.inverse T‖*‖T (R v)‖ := (Ring.inverse T).le_opNorm _
      _ ≤ κ*‖T (R v)‖ := mul_le_mul_of_nonneg_right hi (norm_nonneg _)
      _ = κ*‖μ‖*‖R v‖ := by rw [hr, norm_smul]; ring
  have hmul : 1 ≤ κ*‖μ‖ := (mul_le_mul_iff_right₀ (norm_pos_iff.mpr hRne)).mp (by simpa [mul_comm] using hn)
  rw [inv_eq_one_div]
  exact (div_le_iff₀ hκ).mpr (by nlinarith)

/-- The exact zero padding's spectral gap is derived from the original inverse. -/
theorem zeroExtend_spectral_gap (f : D ↪ P) (A : Matrix D D ℂ)
    (hA : IsUnit A) (hH : (Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ)
      (zeroExtend f A)).toLinearMap.IsSymmetric)
    {κ : ℝ} (hκ : 0 < κ) (hinv : ‖Ring.inverse A‖ ≤ κ)
    (i : Fin (Module.finrank ℂ (EuclideanSpace ℂ P))) :
    hH.eigenvalues rfl i = 0 ∨ κ⁻¹ ≤ |hH.eigenvalues rfl i| := by
  by_cases hi : hH.eigenvalues rfl i = 0
  · exact Or.inl hi
  · right
    have he := hH.hasEigenvector_eigenvectorBasis rfl i
    have hb := zeroExtend_nonzero_eigenvalue_gap f A hA hκ hinv
      (μ := (hH.eigenvalues rfl i : ℂ)) (by simpa only [Complex.ofReal_ne_zero] using hi)
      _ he.2 (Module.End.mem_eigenspace_iff.mp he.1)
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hb

end Physical
end OptimalQLS.PhysicalRobustness
